/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::HyperscanError,
  flags::ScanFlags,
  hs,
  matchers::{ByteSlice, ExpressionIndex, MatchEvent, MatchResult},
  state::Scratch,
};

use displaydoc::Display;
use thiserror::Error;
use tokio::sync::mpsc;

use std::{
  mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
};


#[derive(Debug)]
pub struct StreamMatch {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub flags: ScanFlags,
}

pub trait StreamScanner = FnMut(&StreamMatch) -> MatchResult;

pub(crate) struct StreamMatcher<'code> {
  pub matches_tx: mpsc::Sender<StreamMatch>,
  pub handler: &'code mut dyn StreamScanner,
}

impl<'code> StreamMatcher<'code> {
  #[inline(always)]
  pub fn push_new_match(&self, m: StreamMatch) { self.matches_tx.blocking_send(m).unwrap(); }

  #[inline(always)]
  pub fn handle_match(&mut self, m: &StreamMatch) -> MatchResult { (self.handler)(m) }

  #[inline]
  fn mut_handler(&self) -> &'code mut dyn StreamScanner {
    let handler: &dyn StreamScanner = &self.handler;
    let handler: *const dyn StreamScanner = handler;
    let handler: &'code mut dyn StreamScanner =
      unsafe { &mut *mem::transmute::<_, *mut dyn StreamScanner>(handler) };
    handler
  }
}

impl<'code> Clone for StreamMatcher<'code> {
  fn clone(&self) -> Self {
    Self {
      matches_tx: self.matches_tx.clone(),
      handler: self.mut_handler(),
    }
  }
}

pub struct CompressedStream<'db, 'code> {
  buf: Vec<c_char>,
  scratch: Pin<&'db mut Scratch<'db>>,
  matcher: StreamMatcher<'code>,
}

impl<'db, 'code> CompressedStream<'db, 'code> {
  pub fn reserve(&mut self, limit: usize) {
    if limit <= self.space() {
      return;
    }
    let additional = limit - self.space();
    self.buf.reserve(additional);
  }

  fn ref_scratch_ptr(&self) -> *mut Scratch {
    let scratch: &Scratch<'db> = self.scratch.as_ref().get_ref();
    let scratch: *const Scratch = scratch;
    let scratch: *mut Scratch = unsafe { mem::transmute(scratch) };
    scratch
  }

  fn pin_scratch(&self) -> Pin<&'db mut Scratch<'db>> {
    let scratch: *mut Scratch<'db> = unsafe { mem::transmute(self.ref_scratch_ptr()) };
    let scratch: &'db mut Scratch<'db> = unsafe { &mut *scratch };
    Pin::new(scratch)
  }

  fn ref_matcher_context(&self) -> *mut c_void {
    let matcher: *const StreamMatcher = &self.matcher;
    let matcher: *mut StreamMatcher = unsafe { mem::transmute(matcher) };
    let matcher = matcher as usize;
    matcher as *mut c_void
  }

  #[inline]
  pub fn as_mut_ptr(&mut self) -> *mut c_char { self.buf.as_mut_ptr() }

  #[inline]
  pub fn as_ptr(&self) -> *const c_char { self.buf.as_ptr() }

  #[inline]
  pub fn space(&self) -> usize { self.buf.capacity() }

  pub fn expand(&self) -> Result<Stream<'db, 'code>, HyperscanError> {
    let mut inner = ptr::null_mut();
    HyperscanError::from_native(unsafe {
      hs::hs_expand_stream(
        self.pin_scratch().into_ref().pinned_db().get_ref().as_ref(),
        &mut inner,
        self.as_ptr(),
        self.space(),
      )
    })?;
    Ok(Stream {
      inner,
      scratch: self.pin_scratch(),
      matcher: self.matcher.clone(),
    })
  }

  pub fn expand_and_reset(&self) -> Result<Stream<'db, 'code>, HyperscanError> {
    let mut stream = mem::MaybeUninit::<hs::hs_stream>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_reset_and_expand_stream(
        stream.as_mut_ptr(),
        self.as_ptr(),
        self.space(),
        self.pin_scratch().get_mut().as_mut(),
        Some(match_slice_stream),
        self.ref_matcher_context(),
      )
    })?;
    Ok(Stream {
      inner: stream.as_mut_ptr(),
      scratch: self.pin_scratch(),
      matcher: self.matcher.clone(),
    })
  }
}

pub enum CompressReserveBehavior<'db, 'code> {
  NewBuf,
  ExpandBuf(CompressedStream<'db, 'code>),
  FixedSizeBuf(CompressedStream<'db, 'code>),
}

pub(crate) enum ReserveResponse<'db, 'code> {
  MadeSpace(CompressedStream<'db, 'code>),
  NoSpace(CompressedStream<'db, 'code>),
}

impl<'db, 'code> CompressReserveBehavior<'db, 'code> {
  pub(crate) fn reserve(
    self,
    scratch: Pin<&'db mut Scratch<'db>>,
    matcher: &StreamMatcher<'code>,
    n: usize,
  ) -> ReserveResponse<'db, 'code> {
    match self {
      Self::NewBuf => ReserveResponse::MadeSpace(CompressedStream {
        buf: Vec::with_capacity(n),
        scratch,
        matcher: matcher.clone(),
      }),
      Self::ExpandBuf(mut buf) => {
        buf.reserve(n);
        ReserveResponse::MadeSpace(buf)
      },
      Self::FixedSizeBuf(buf) => {
        if buf.space() <= n {
          ReserveResponse::NoSpace(buf)
        } else {
          ReserveResponse::MadeSpace(buf)
        }
      },
    }
  }
}

#[derive(Debug, Display, Error)]
pub enum CompressionError {
  /// other error: {0}
  Other(#[from] HyperscanError),
  /// not enough space for {0} in buf
  NoSpace(usize),
}

pub struct Stream<'db, 'code> {
  inner: *mut hs::hs_stream,
  scratch: Pin<&'db mut Scratch<'db>>,
  matcher: StreamMatcher<'code>,
}

impl<'db, 'code> Stream<'db, 'code> {
  pub fn open<const N: usize, F: StreamScanner>(
    scratch: Pin<&'db mut Scratch<'db>>,
    flags: ScanFlags,
    f: &'code mut F,
  ) -> Result<(Self, mpsc::Receiver<StreamMatch>), HyperscanError> {
    let (matches_tx, matches_rx) = mpsc::channel(N);
    let mut stream_ptr = ptr::null_mut();
    let db: Pin<&'db Database> = scratch.as_ref().pinned_db();
    HyperscanError::from_native(unsafe {
      hs::hs_open_stream(db.get_ref().as_ref(), flags.into_native(), &mut stream_ptr)
    })?;
    let matcher = StreamMatcher {
      matches_tx,
      handler: f,
    };
    let s = Self {
      inner: stream_ptr,
      scratch,
      matcher,
    };
    Ok((s, matches_rx))
  }

  fn ref_scratch_ptr(&self) -> *mut Scratch {
    let scratch: &Scratch<'db> = self.scratch.as_ref().get_ref();
    let scratch: *const Scratch = scratch;
    let scratch: *mut Scratch = unsafe { mem::transmute(scratch) };
    scratch
  }

  fn pin_scratch(&self) -> Pin<&'db mut Scratch<'db>> {
    let scratch: *mut Scratch<'db> = unsafe { mem::transmute(self.ref_scratch_ptr()) };
    let scratch: &'db mut Scratch<'db> = unsafe { &mut *scratch };
    Pin::new(scratch)
  }

  fn ref_matcher_context(&self) -> *mut c_void {
    let matcher: *const StreamMatcher = &self.matcher;
    let matcher: *mut StreamMatcher = unsafe { mem::transmute(matcher) };
    let matcher = matcher as usize;
    matcher as *mut c_void
  }

  fn stream_ptr(self: Pin<&mut Self>) -> *mut hs::hs_stream { self.get_mut().as_mut() }

  fn scratch_ptr(mut self: Pin<&mut Self>) -> *mut hs::hs_scratch {
    self.scratch.as_mut().get_mut().as_mut()
  }

  pub fn scan(
    mut self: Pin<&mut Self>,
    data: ByteSlice<'_>,
    flags: ScanFlags,
  ) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      let matcher_context = self.ref_matcher_context();
      hs::hs_scan_stream(
        self.as_mut().stream_ptr(),
        data.as_ptr(),
        data.native_len(),
        flags.into_native(),
        self.scratch_ptr(),
        Some(match_slice_stream),
        matcher_context,
      )
    })
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanError> {
    let mut stream_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe { hs::hs_copy_stream(&mut stream_ptr, self.as_ref()) })?;
    Ok(Self {
      inner: stream_ptr,
      scratch: self.pin_scratch(),
      matcher: self.matcher.clone(),
    })
  }

  fn try_drop(mut self: Pin<&mut Self>) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_close_stream(
        self.as_mut().stream_ptr(),
        self.as_mut().scratch_ptr(),
        Some(match_slice_stream),
        self.ref_matcher_context(),
      )
    })
  }

  pub fn try_reset(mut self: Pin<&mut Self>, flags: ScanFlags) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_reset_stream(
        self.as_mut().stream_ptr(),
        flags.into_native(),
        self.as_mut().scratch_ptr(),
        Some(match_slice_stream),
        self.ref_matcher_context(),
      )
    })
  }

  pub fn try_reset_and_clone(&self) -> Result<Self, HyperscanError> {
    let mut stream = mem::MaybeUninit::<hs::hs_stream>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_reset_and_copy_stream(
        stream.as_mut_ptr(),
        self.as_ref(),
        self.pin_scratch().get_mut().as_mut(),
        Some(match_slice_stream),
        self.ref_matcher_context(),
      )
    })?;
    Ok(Self {
      inner: stream.as_mut_ptr(),
      scratch: self.pin_scratch(),
      matcher: self.matcher.clone(),
    })
  }

  #[inline]
  pub fn required_compress_space(&self) -> Result<usize, HyperscanError> {
    let mut used_space = mem::MaybeUninit::<usize>::uninit();
    assert_eq!(
      Err(HyperscanError::InsufficientSpace),
      HyperscanError::from_native(unsafe {
        hs::hs_compress_stream(self.as_ref(), ptr::null_mut(), 0, used_space.as_mut_ptr())
      })
    );
    Ok(unsafe { used_space.assume_init() })
  }

  pub fn compress_into(
    &self,
    buf: CompressReserveBehavior<'db, 'code>,
  ) -> Result<CompressedStream<'db, 'code>, CompressionError> {
    let mut used_space = self.required_compress_space()?;
    let mut buf = match buf.reserve(self.pin_scratch(), &self.matcher, used_space) {
      ReserveResponse::NoSpace(_) => return Err(CompressionError::NoSpace(used_space)),
      ReserveResponse::MadeSpace(buf) => buf,
    };
    assert!(used_space <= buf.space());
    HyperscanError::from_native(unsafe {
      hs::hs_compress_stream(
        self.as_ref(),
        buf.as_mut_ptr(),
        buf.space(),
        &mut used_space,
      )
    })?;
    Ok(buf)
  }
}

impl<'db, 'code> AsRef<hs::hs_stream> for Stream<'db, 'code> {
  fn as_ref(&self) -> &hs::hs_stream { unsafe { &*self.inner } }
}

impl<'db, 'code> AsMut<hs::hs_stream> for Stream<'db, 'code> {
  fn as_mut(&mut self) -> &mut hs::hs_stream { unsafe { &mut *self.inner } }
}

impl<'db, 'code> Clone for Stream<'db, 'code> {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl<'db, 'code> ops::Drop for Stream<'db, 'code> {
  fn drop(&mut self) { Pin::new(self).try_drop().unwrap(); }
}

unsafe extern "C" fn match_slice_stream(
  id: c_uint,
  from: c_ulonglong,
  to: c_ulonglong,
  flags: c_uint,
  context: *mut c_void,
) -> c_int {
  let MatchEvent {
    id,
    range,
    flags,
    context,
  } = MatchEvent::coerce_args(id, from, to, flags, context);
  let mut matcher: Pin<&mut StreamMatcher> =
    MatchEvent::extract_context::<'_, StreamMatcher>(context).unwrap();
  let m = StreamMatch { id, range, flags };

  let result = matcher.handle_match(&m);
  if result == MatchResult::Continue {
    matcher.push_new_match(m);
  }

  result.into_native()
}

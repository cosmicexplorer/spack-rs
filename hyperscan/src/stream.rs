/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::HyperscanError,
  flags::ScanFlags,
  hs,
  matchers::{ByteSlice, ExpressionIndex, MatchEvent, MatchResult},
  state::{HandleOps, ResourceOps, Scratch},
};

use displaydoc::Display;
use thiserror::Error;
use tokio::{sync::mpsc, task};

use std::{
  marker::PhantomData,
  mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
  sync::Arc,
};


#[derive(Debug)]
pub struct StreamMatch {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub flags: ScanFlags,
}

pub trait StreamScanner {
  fn stream_scan(&mut self, m: &StreamMatch) -> MatchResult;
}

pub(crate) struct StreamMatcher<S> {
  pub matches_tx: mpsc::Sender<StreamMatch>,
  pub handler: S,
}

impl<S: StreamScanner> StreamMatcher<S> {
  #[inline(always)]
  pub fn push_new_match(&mut self, m: StreamMatch) { self.matches_tx.blocking_send(m).unwrap(); }

  #[inline(always)]
  pub fn handle_match(&mut self, m: &StreamMatch) -> MatchResult { (self.handler).stream_scan(m) }
}

impl<S: Clone> Clone for StreamMatcher<S> {
  fn clone(&self) -> Self {
    Self {
      matches_tx: self.matches_tx.clone(),
      handler: self.handler.clone(),
    }
  }
}

/* pub struct CompressedStream<'db, 'code> { */
/* buf: Vec<c_char>, */
/* scratch: Pin<&'db mut Scratch<'db>>, */
/* matcher: StreamMatcher<'code>, */
/* } */

/* impl<'db, 'code> CompressedStream<'db, 'code> { */
/* pub fn reserve(&mut self, limit: usize) { */
/* if limit <= self.space() { */
/* return; */
/* } */
/* let additional = limit - self.space(); */
/* self.buf.reserve(additional); */
/* } */

/* fn ref_scratch_ptr(&self) -> *mut Scratch { */
/* let scratch: &Scratch<'db> = self.scratch.as_ref().get_ref(); */
/* let scratch: *const Scratch = scratch; */
/* let scratch: *mut Scratch = unsafe { mem::transmute(scratch) }; */
/* scratch */
/* } */

/* fn pin_scratch(&self) -> Pin<&'db mut Scratch<'db>> { */
/* let scratch: *mut Scratch<'db> = unsafe {
 * mem::transmute(self.ref_scratch_ptr()) }; */
/* let scratch: &'db mut Scratch<'db> = unsafe { &mut *scratch }; */
/* Pin::new(scratch) */
/* } */

/* fn ref_matcher_context(&self) -> *mut c_void { */
/* let matcher: *const StreamMatcher = &self.matcher; */
/* let matcher: *mut StreamMatcher = unsafe { mem::transmute(matcher) }; */
/* let matcher = matcher as usize; */
/* matcher as *mut c_void */
/* } */

/* #[inline] */
/* pub fn as_mut_ptr(&mut self) -> *mut c_char { self.buf.as_mut_ptr() } */

/* #[inline] */
/* pub fn as_ptr(&self) -> *const c_char { self.buf.as_ptr() } */

/* #[inline] */
/* pub fn space(&self) -> usize { self.buf.capacity() } */

/* /\* pub fn expand(&self) -> Result<Stream<'db, 'code>, HyperscanError> {
 * *\/ */
/* /\*   let mut inner = ptr::null_mut(); *\/ */
/* /\*   HyperscanError::from_native(unsafe { *\/ */
/* /\*     hs::hs_expand_stream( *\/ */
/* /\*       self.pin_scratch().into_ref().pinned_db().get_ref().as_ref(),
 * *\/ */
/* /\*       &mut inner, *\/ */
/* /\*       self.as_ptr(), *\/ */
/* /\*       self.space(), *\/ */
/* /\*     ) *\/ */
/* /\*   })?; *\/ */
/* /\*   Ok(Stream { *\/ */
/* /\*     inner, *\/ */
/* /\*     scratch: self.pin_scratch(), *\/ */
/* /\*     matcher: self.matcher.clone(), *\/ */
/* /\*   }) *\/ */
/* /\* } *\/ */

/* /\* pub fn expand_and_reset(&self) -> Result<Stream<'db, 'code>,
 * HyperscanError> { *\/ */
/* /\*   let mut stream = mem::MaybeUninit::<hs::hs_stream>::uninit(); *\/ */
/* /\*   HyperscanError::from_native(unsafe { *\/ */
/* /\*     hs::hs_reset_and_expand_stream( *\/ */
/* /\*       stream.as_mut_ptr(), *\/ */
/* /\*       self.as_ptr(), *\/ */
/* /\*       self.space(), *\/ */
/* /\*       self.pin_scratch().get_mut().as_mut(), *\/ */
/* /\*       Some(match_slice_stream), *\/ */
/* /\*       self.ref_matcher_context(), *\/ */
/* /\*     ) *\/ */
/* /\*   })?; *\/ */
/* /\*   Ok(Stream { *\/ */
/* /\*     inner: stream.as_mut_ptr(), *\/ */
/* /\*     scratch: self.pin_scratch(), *\/ */
/* /\*     matcher: self.matcher.clone(), *\/ */
/* /\*   }) *\/ */
/* /\* } *\/ */
/* } */

/* pub enum CompressReserveBehavior<'db, 'code> { */
/* NewBuf, */
/* ExpandBuf(CompressedStream<'db, 'code>), */
/* FixedSizeBuf(CompressedStream<'db, 'code>), */
/* } */

/* pub(crate) enum ReserveResponse<'db, 'code> { */
/* MadeSpace(CompressedStream<'db, 'code>), */
/* NoSpace(CompressedStream<'db, 'code>), */
/* } */

/* impl<'db, 'code> CompressReserveBehavior<'db, 'code> { */
/* pub(crate) fn reserve( */
/* self, */
/* scratch: Pin<&'db mut Scratch<'db>>, */
/* matcher: &StreamMatcher<'code>, */
/* n: usize, */
/* ) -> ReserveResponse<'db, 'code> { */
/* match self { */
/* Self::NewBuf => ReserveResponse::MadeSpace(CompressedStream { */
/* buf: Vec::with_capacity(n), */
/* scratch, */
/* matcher: matcher.clone(), */
/* }), */
/* Self::ExpandBuf(mut buf) => { */
/* buf.reserve(n); */
/* ReserveResponse::MadeSpace(buf) */
/* }, */
/* Self::FixedSizeBuf(buf) => { */
/* if buf.space() <= n { */
/* ReserveResponse::NoSpace(buf) */
/* } else { */
/* ReserveResponse::MadeSpace(buf) */
/* } */
/* }, */
/* } */
/* } */
/* } */

/* #[derive(Debug, Display, Error)] */
/* pub enum CompressionError { */
/* /// other error: {0} */
/* Other(#[from] HyperscanError), */
/* /// not enough space for {0} in buf */
/* NoSpace(usize), */
/* } */

pub struct LiveStream<'db> {
  inner: *mut hs::hs_stream,
  _ph: PhantomData<&'db u8>,
}

impl<'db> AsRef<hs::hs_stream> for LiveStream<'db> {
  fn as_ref(&self) -> &hs::hs_stream { unsafe { &*self.inner } }
}

impl<'db> AsMut<hs::hs_stream> for LiveStream<'db> {
  fn as_mut(&mut self) -> &mut hs::hs_stream { unsafe { &mut *self.inner } }
}

pub trait StreamOps: ResourceOps {
  fn try_reset(&mut self) -> Result<(), Self::Err>;
  fn try_reset_and_copy(&self) -> Result<Self::Container, Self::Err>;
}

impl<'db> HandleOps for LiveStream<'db> {
  type Container = Self;
  type Err = HyperscanError;

  fn try_clone(&self) -> Result<Self, HyperscanError> {
    let mut stream_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe { hs::hs_copy_stream(&mut stream_ptr, self.as_ref()) })?;
    Ok(Self {
      inner: stream_ptr,
      _ph: PhantomData,
    })
  }
}

impl<'db> ResourceOps for LiveStream<'db> {
  type Params = (ScanFlags, &'db Database);

  fn try_open(p: (ScanFlags, &'db Database)) -> Result<Self, HyperscanError> {
    let (flags, db) = p;
    let mut stream_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe {
      hs::hs_open_stream(db.as_ref(), flags.into_native(), &mut stream_ptr)
    })?;
    Ok(Self {
      inner: stream_ptr,
      _ph: PhantomData,
    })
  }

  fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_close_stream(self.as_mut(), ptr::null_mut(), None, ptr::null_mut())
    })
  }
}

impl<'db> StreamOps for LiveStream<'db> {
  fn try_reset(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_reset_stream(
        self.as_mut(),
        ScanFlags::default().into_native(),
        ptr::null_mut(),
        None,
        ptr::null_mut(),
      )
    })
  }

  fn try_reset_and_copy(&self) -> Result<Self, HyperscanError> {
    let mut to = mem::MaybeUninit::<hs::hs_stream>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_reset_and_copy_stream(
        to.as_mut_ptr(),
        self.as_ref(),
        ptr::null_mut(),
        None,
        ptr::null_mut(),
      )
    })?;
    Ok(Self {
      inner: to.as_mut_ptr(),
      _ph: PhantomData,
    })
  }
}

impl<'db> ops::Drop for LiveStream<'db> {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

impl<'db> Clone for LiveStream<'db> {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

pub struct StreamSink<'db, S> {
  live: LiveStream<'db>,
  scratch: Arc<Scratch<'db>>,
  matcher: StreamMatcher<S>,
}

impl<'db, S: Clone> HandleOps for StreamSink<'db, S> {
  type Container = Self;
  type Err = HyperscanError;

  fn try_clone(&self) -> Result<Self, HyperscanError> {
    Ok(Self {
      live: self.live.try_clone()?,
      scratch: self.scratch.clone(),
      matcher: self.matcher.clone(),
    })
  }
}

#[derive(Clone)]
struct AcceptMatches;

impl StreamScanner for AcceptMatches {
  fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult { MatchResult::Continue }
}

impl<'db> StreamSink<'db, AcceptMatches> {
  pub async fn scan(
    &mut self,
    data: ByteSlice<'_>,
    flags: ScanFlags,
  ) -> Result<(), HyperscanError> {
    let data_len = data.native_len();
    let data = data.as_ptr() as usize;
    let s: *mut Self = self;
    let s = s as usize;

    task::spawn_blocking(move || {
      let Self {
        live,
        scratch,
        matcher,
      } = unsafe { &mut *(s as *mut Self) };
      let matcher: *mut StreamMatcher<AcceptMatches> = matcher;
      let matcher = matcher as usize;
      HyperscanError::from_native(unsafe {
        hs::hs_scan_stream(
          live.as_mut(),
          data as *const c_char,
          data_len,
          flags.into_native(),
          Arc::make_mut(scratch).as_mut(),
          Some(match_slice_stream),
          matcher as *mut c_void,
        )
      })
    })
    .await
    .unwrap()
  }
}

pub struct Streamer<'db, S> {
  pub sink: StreamSink<'db, S>,
  pub rx: mpsc::Receiver<StreamMatch>,
}

/* impl<'db, 'code> Stream<'db, 'code> { */
/* pub fn open<const N: usize, F: StreamScanner>( */
/* scratch: Pin<&'db mut Scratch<'db>>, */
/* flags: ScanFlags, */
/* f: &'code mut F, */
/* ) -> Result<(Self, mpsc::Receiver<StreamMatch>), HyperscanError> { */
/* let (matches_tx, matches_rx) = mpsc::channel(N); */
/* let mut stream_ptr = ptr::null_mut(); */
/* let db: Pin<&'db Database> = scratch.as_ref().pinned_db(); */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_open_stream(db.get_ref().as_ref(), flags.into_native(), &mut
 * stream_ptr) */
/* })?; */
/* let matcher = StreamMatcher { */
/* matches_tx, */
/* handler: f, */
/* }; */
/* let s = Self { */
/* inner: stream_ptr, */
/* scratch, */
/* matcher, */
/* }; */
/* Ok((s, matches_rx)) */
/* } */

/* fn ref_scratch_ptr(&self) -> *mut Scratch { */
/* let scratch: &Scratch<'db> = self.scratch.as_ref().get_ref(); */
/* let scratch: *const Scratch = scratch; */
/* let scratch: *mut Scratch = unsafe { mem::transmute(scratch) }; */
/* scratch */
/* } */

/* fn pin_scratch(&self) -> Pin<&'db mut Scratch<'db>> { */
/* let scratch: *mut Scratch<'db> = unsafe {
 * mem::transmute(self.ref_scratch_ptr()) }; */
/* let scratch: &'db mut Scratch<'db> = unsafe { &mut *scratch }; */
/* Pin::new(scratch) */
/* } */

/* fn ref_matcher_context(&self) -> *mut c_void { */
/* let matcher: *const StreamMatcher = &self.matcher; */
/* let matcher: *mut StreamMatcher = unsafe { mem::transmute(matcher) }; */
/* let matcher = matcher as usize; */
/* matcher as *mut c_void */
/* } */

/* fn stream_ptr(self: Pin<&mut Self>) -> *mut hs::hs_stream {
 * self.get_mut().as_mut() } */

/* fn scratch_ptr(mut self: Pin<&mut Self>) -> *mut hs::hs_scratch { */
/* self.scratch.as_mut().get_mut().as_mut() */
/* } */

/* pub fn scan( */
/* mut self: Pin<&mut Self>, */
/* data: ByteSlice<'_>, */
/* flags: ScanFlags, */
/* ) -> Result<(), HyperscanError> { */
/* HyperscanError::from_native(unsafe { */
/* let matcher_context = self.ref_matcher_context(); */
/* hs::hs_scan_stream( */
/* self.as_mut().stream_ptr(), */
/* data.as_ptr(), */
/* data.native_len(), */
/* flags.into_native(), */
/* self.scratch_ptr(), */
/* Some(match_slice_stream), */
/* matcher_context, */
/* ) */
/* }) */
/* } */

/* pub fn try_clone(&self) -> Result<Self, HyperscanError> { */
/* let mut stream_ptr = ptr::null_mut(); */
/* HyperscanError::from_native(unsafe { hs::hs_copy_stream(&mut stream_ptr,
 * self.as_ref()) })?; */
/* Ok(Self { */
/* inner: stream_ptr, */
/* scratch: self.pin_scratch(), */
/* matcher: self.matcher.clone(), */
/* }) */
/* } */

/* fn try_drop(mut self: Pin<&mut Self>) -> Result<(), HyperscanError> { */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_close_stream( */
/* self.as_mut().stream_ptr(), */
/* self.as_mut().scratch_ptr(), */
/* Some(match_slice_stream), */
/* self.ref_matcher_context(), */
/* ) */
/* }) */
/* } */

/* pub fn try_reset(mut self: Pin<&mut Self>, flags: ScanFlags) -> Result<(),
 * HyperscanError> { */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_reset_stream( */
/* self.as_mut().stream_ptr(), */
/* flags.into_native(), */
/* self.as_mut().scratch_ptr(), */
/* Some(match_slice_stream), */
/* self.ref_matcher_context(), */
/* ) */
/* }) */
/* } */

/* pub fn try_reset_and_clone(&self) -> Result<Self, HyperscanError> { */
/* let mut stream = mem::MaybeUninit::<hs::hs_stream>::uninit(); */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_reset_and_copy_stream( */
/* stream.as_mut_ptr(), */
/* self.as_ref(), */
/* self.pin_scratch().get_mut().as_mut(), */
/* Some(match_slice_stream), */
/* self.ref_matcher_context(), */
/* ) */
/* })?; */
/* Ok(Self { */
/* inner: stream.as_mut_ptr(), */
/* scratch: self.pin_scratch(), */
/* matcher: self.matcher.clone(), */
/* }) */
/* } */

/* #[inline] */
/* pub fn required_compress_space(&self) -> Result<usize, HyperscanError> { */
/* let mut used_space = mem::MaybeUninit::<usize>::uninit(); */
/* assert_eq!( */
/* Err(HyperscanError::InsufficientSpace), */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_compress_stream(self.as_ref(), ptr::null_mut(), 0,
 * used_space.as_mut_ptr()) */
/* }) */
/* ); */
/* Ok(unsafe { used_space.assume_init() }) */
/* } */

/* pub fn compress_into( */
/* &self, */
/* buf: CompressReserveBehavior<'db, 'code>, */
/* ) -> Result<CompressedStream<'db, 'code>, CompressionError> { */
/* let mut used_space = self.required_compress_space()?; */
/* let mut buf = match buf.reserve(self.pin_scratch(), &self.matcher,
 * used_space) { */
/* ReserveResponse::NoSpace(_) => return
 * Err(CompressionError::NoSpace(used_space)), */
/* ReserveResponse::MadeSpace(buf) => buf, */
/* }; */
/* assert!(used_space <= buf.space()); */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_compress_stream( */
/* self.as_ref(), */
/* buf.as_mut_ptr(), */
/* buf.space(), */
/* &mut used_space, */
/* ) */
/* })?; */
/* Ok(buf) */
/* } */
/* } */

/* impl<'db, 'code> AsRef<hs::hs_stream> for Stream<'db, 'code> { */
/* fn as_ref(&self) -> &hs::hs_stream { unsafe { &*self.inner } } */
/* } */

/* impl<'db, 'code> AsMut<hs::hs_stream> for Stream<'db, 'code> { */
/* fn as_mut(&mut self) -> &mut hs::hs_stream { unsafe { &mut *self.inner } } */
/* } */

/* impl<'db, 'code> Clone for Stream<'db, 'code> { */
/* fn clone(&self) -> Self { self.try_clone().unwrap() } */
/* } */

/* impl<'db, 'code> ops::Drop for Stream<'db, 'code> { */
/* fn drop(&mut self) { Pin::new(self).try_drop().unwrap(); } */
/* } */

/* pub struct MatchStream<'db, 'code> { */
/* stream: Stream<'db, 'code>, */
/* recv: mpsc::Receiver<StreamMatch>, */
/* } */

/* impl<'db, 'code> MatchStream<'db, 'code> { */
/* pub fn open<const N: usize, F: StreamScanner>( */
/* scratch: Pin<&'db mut Scratch<'db>>, */
/* flags: ScanFlags, */
/* f: &'code mut F, */
/* ) -> Result<Self, HyperscanError> { */
/* let (stream, recv) = Stream::open::<N, F>(scratch, flags, f)?; */
/* Ok(Self { stream, recv }) */
/* } */
/* } */

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
  let mut matcher: Pin<&mut StreamMatcher<AcceptMatches>> =
    MatchEvent::extract_context::<'_, StreamMatcher<AcceptMatches>>(context).unwrap();
  let m = StreamMatch { id, range, flags };

  let result = matcher.handle_match(&m);
  if result == MatchResult::Continue {
    matcher.push_new_match(m);
  }

  result.into_native()
}

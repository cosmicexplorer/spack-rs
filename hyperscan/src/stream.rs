/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  database::Database,
  error::{CompressionError, HyperscanRuntimeError},
  hs,
  matchers::{
    stream::{StreamHandler, StreamMatcher},
    ByteSlice,
  },
  state::Scratch,
};
#[cfg(feature = "async")]
use crate::{error::ScanError, matchers::stream::StreamMatch};

use std::{mem, ops, ptr};

#[derive(Debug)]
#[repr(transparent)]
pub struct LiveStream(*mut hs::hs_stream);

unsafe impl Send for LiveStream {}
unsafe impl Sync for LiveStream {}

pub type NativeStream = hs::hs_stream;

impl LiveStream {
  pub const unsafe fn from_native(p: *mut NativeStream) -> Self { Self(p) }

  pub fn as_ref_native(&self) -> &NativeStream { unsafe { &*self.0 } }

  pub fn as_mut_native(&mut self) -> &mut NativeStream { unsafe { &mut *self.0 } }

  pub fn try_open(db: &Database) -> Result<Self, HyperscanRuntimeError> {
    let mut ret = ptr::null_mut();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_open_stream(
        db.as_ref_native(),
        /* NB: ignoring flags for now! */
        0,
        &mut ret,
      )
    })?;
    Ok(unsafe { Self::from_native(ret) })
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
    let mut ret = ptr::null_mut();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_copy_stream(&mut ret, self.as_ref_native())
    })?;
    Ok(unsafe { Self::from_native(ret) })
  }

  pub fn try_clone_from(&mut self, source: &Self) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_direct_reset_and_copy_stream(self.as_mut_native(), source.as_ref_native())
    })
  }

  pub unsafe fn try_drop(&mut self) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(unsafe { hs::hs_direct_free_stream(self.as_mut_native()) })
  }

  pub fn try_reset(&mut self) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(unsafe { hs::hs_direct_reset_stream(self.as_mut_native()) })
  }

  pub fn compress(
    &self,
    into: compress::CompressReserveBehavior,
  ) -> Result<compress::CompressedStream, CompressionError> {
    compress::CompressedStream::compress(into, self)
  }
}

impl Clone for LiveStream {
  fn clone(&self) -> Self { self.try_clone().unwrap() }

  fn clone_from(&mut self, source: &Self) { self.try_clone_from(source).unwrap(); }
}

impl ops::Drop for LiveStream {
  fn drop(&mut self) {
    unsafe {
      self.try_drop().unwrap();
    }
  }
}

pub struct StreamSink {
  pub live: LiveStream,
  pub matcher: StreamMatcher,
}

impl StreamSink {
  pub fn new<S: StreamHandler+'static>(live: LiveStream) -> Self {
    Self {
      live,
      matcher: StreamMatcher::new::<S>(),
    }
  }

  pub fn scan<'data>(
    &mut self,
    data: ByteSlice<'data>,
    scratch: &mut Scratch,
  ) -> Result<(), HyperscanRuntimeError> {
    scratch.scan_sync_stream(data, self)
  }

  pub fn flush_eod(&mut self, scratch: &mut Scratch) -> Result<(), HyperscanRuntimeError> {
    scratch.flush_eod_sync(self)
  }

  pub fn try_reset(&mut self) -> Result<(), HyperscanRuntimeError> {
    self.live.try_reset()?;
    self.matcher.reset();
    Ok(())
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
    Ok(Self {
      live: self.live.try_clone()?,
      matcher: self.matcher.clone(),
    })
  }

  pub fn try_clone_from(&mut self, other: &Self) -> Result<(), HyperscanRuntimeError> {
    self.live.try_clone_from(&other.live)?;
    self.matcher.clone_from(&other.matcher);
    Ok(())
  }
}

impl Clone for StreamSink {
  fn clone(&self) -> Self { self.try_clone().unwrap() }

  fn clone_from(&mut self, other: &Self) { self.try_clone_from(other).unwrap(); }
}

pub struct ScratchStreamSink {
  pub sink: StreamSink,
  pub scratch: Scratch,
}

impl ScratchStreamSink {
  pub fn scan<'data>(&mut self, data: ByteSlice<'data>) -> Result<(), HyperscanRuntimeError> {
    let Self { sink, scratch } = self;
    sink.scan(data, scratch)
  }

  pub fn flush_eod(&mut self) -> Result<(), HyperscanRuntimeError> {
    let Self { sink, scratch } = self;
    sink.flush_eod(scratch)
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
    Ok(Self {
      sink: self.sink.try_clone()?,
      scratch: self.scratch.try_clone()?,
    })
  }
}

impl Clone for ScratchStreamSink {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl std::io::Write for ScratchStreamSink {
  fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
    self
      .scan(ByteSlice::from_slice(buf))
      .map(|()| buf.len())
      .map_err(std::io::Error::other)
  }

  fn flush(&mut self) -> std::io::Result<()> { Ok(()) }
}

#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
pub mod channel {
  use super::*;
  use crate::matchers::stream::scan::{StreamScanMatcher, StreamScanner};

  use futures_util::TryFutureExt;
  use tokio::{io, sync::mpsc};

  use std::{
    future::Future,
    mem,
    pin::Pin,
    slice,
    task::{ready, Context, Poll},
  };

  pub struct StreamSinkChannel {
    pub live: LiveStream,
    pub matcher: StreamScanMatcher,
    pub rx: mpsc::UnboundedReceiver<StreamMatch>,
  }

  impl StreamSinkChannel {
    pub fn new<S: StreamScanner+'static>(live: LiveStream) -> Self {
      let (tx, rx) = mpsc::unbounded_channel();
      Self {
        live,
        matcher: StreamScanMatcher::new::<S>(tx),
        rx,
      }
    }

    pub async fn scan<'data>(
      &mut self,
      data: ByteSlice<'data>,
      scratch: &mut Scratch,
    ) -> Result<(), ScanError> {
      scratch.scan_stream(data, self).await
    }

    pub async fn flush_eod(&mut self, scratch: &mut Scratch) -> Result<(), ScanError> {
      scratch.flush_eod(self).await
    }

    pub fn try_reset(&mut self) -> Result<(), HyperscanRuntimeError> {
      self.live.try_reset()?;
      self.matcher.reset();
      Ok(())
    }

    pub fn reset_channel(
      &mut self,
    ) -> (
      mpsc::UnboundedSender<StreamMatch>,
      mpsc::UnboundedReceiver<StreamMatch>,
    ) {
      let (tx, rx) = mpsc::unbounded_channel();
      let old_tx = self.matcher.replace_sender(tx);
      let old_rx = mem::replace(&mut self.rx, rx);
      (old_tx, old_rx)
    }

    pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
      let (tx, rx) = mpsc::unbounded_channel();
      Ok(Self {
        live: self.live.try_clone()?,
        matcher: self.matcher.clone_with_sender(tx),
        rx,
      })
    }

    pub fn try_clone_from(
      &mut self,
      other: &Self,
    ) -> Result<mpsc::UnboundedReceiver<StreamMatch>, HyperscanRuntimeError> {
      let (tx, rx) = mpsc::unbounded_channel();
      self.live.try_clone_from(&other.live)?;
      self.matcher = other.matcher.clone_with_sender(tx);
      Ok(mem::replace(&mut self.rx, rx))
    }
  }

  impl Clone for StreamSinkChannel {
    fn clone(&self) -> Self { self.try_clone().unwrap() }

    fn clone_from(&mut self, other: &Self) { self.try_clone_from(other).unwrap(); }
  }

  pub struct ScratchStreamSinkChannel {
    pub sink: StreamSinkChannel,
    pub scratch: Scratch,
    #[allow(clippy::type_complexity)]
    write_future: Option<(*const u8, Pin<Box<dyn Future<Output=io::Result<usize>>>>)>,
    shutdown_future: Option<Pin<Box<dyn Future<Output=io::Result<()>>>>>,
  }

  unsafe impl Send for ScratchStreamSinkChannel {}
  unsafe impl Sync for ScratchStreamSinkChannel {}

  impl ScratchStreamSinkChannel {
    pub fn new(sink: StreamSinkChannel, scratch: Scratch) -> Self {
      Self {
        sink,
        scratch,
        write_future: None,
        shutdown_future: None,
      }
    }

    pub async fn scan<'data>(&mut self, data: ByteSlice<'data>) -> Result<(), ScanError> {
      let Self { sink, scratch, .. } = self;
      sink.scan(data, scratch).await
    }

    pub async fn flush_eod(&mut self) -> Result<(), ScanError> {
      let Self { sink, scratch, .. } = self;
      sink.flush_eod(scratch).await
    }

    pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
      Ok(Self {
        sink: self.sink.try_clone()?,
        scratch: self.scratch.try_clone()?,
        write_future: None,
        shutdown_future: None,
      })
    }
  }

  impl Clone for ScratchStreamSinkChannel {
    fn clone(&self) -> Self { self.try_clone().unwrap() }
  }

  impl io::AsyncWrite for ScratchStreamSinkChannel {
    fn poll_write(
      mut self: Pin<&mut Self>,
      cx: &mut Context<'_>,
      buf: &[u8],
    ) -> Poll<io::Result<usize>> {
      if self.write_future.is_some() {
        let mut s = self.as_mut();

        let (p, fut) = s.write_future.as_mut().unwrap();
        /* Sequential .poll_write() calls MUST be for the same buffer! */
        assert_eq!(*p, buf.as_ptr());

        let ret = ready!(fut.as_mut().poll(cx));

        s.write_future = None;

        Poll::Ready(ret)
      } else {
        let s: *mut Self = self.as_mut().get_mut();
        let buf_ptr = buf.as_ptr();
        let buf_len = buf.len();
        let mut fut: Pin<Box<dyn Future<Output=io::Result<usize>>>> = Box::pin(
          unsafe { &mut *s }
            .scan(ByteSlice::from_slice(unsafe {
              slice::from_raw_parts(buf_ptr, buf_len)
            }))
            .and_then(move |()| async move { Ok(buf_len) })
            .map_err(io::Error::other),
        );

        if let Poll::Ready(ret) = fut.as_mut().poll(cx) {
          return Poll::Ready(ret);
        }

        self.write_future = Some((buf_ptr, fut));

        Poll::Pending
      }
    }

    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
      Poll::Ready(Ok(()))
    }

    fn poll_shutdown(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
      if self.shutdown_future.is_some() {
        let ret = ready!(self
          .as_mut()
          .shutdown_future
          .as_mut()
          .unwrap()
          .as_mut()
          .poll(cx));

        self.shutdown_future = None;

        Poll::Ready(ret)
      } else {
        let s: *mut Self = self.as_mut().get_mut();
        let mut fut: Pin<Box<dyn Future<Output=io::Result<()>>>> =
          Box::pin(unsafe { &mut *s }.flush_eod().map_err(io::Error::other));

        if let Poll::Ready(ret) = fut.as_mut().poll(cx) {
          return Poll::Ready(ret);
        }

        self.shutdown_future = Some(fut);

        Poll::Pending
      }
    }

    /* TODO: add vectored write support if vectored streaming databases ever
     * exist! */
  }
}

pub mod compress {
  use super::*;

  pub enum CompressReserveBehavior {
    NewBuf,
    ExpandBuf(Vec<u8>),
    FixedSizeBuf(Vec<u8>),
  }

  impl CompressReserveBehavior {
    pub fn current_buf(&mut self) -> Option<&mut Vec<u8>> {
      match self {
        Self::NewBuf => None,
        Self::ExpandBuf(ref mut buf) => Some(buf),
        Self::FixedSizeBuf(ref mut buf) => Some(buf),
      }
    }
  }

  pub(crate) enum ReserveResponse {
    MadeSpace(Vec<u8>),
    NoSpace(Vec<u8>),
  }

  impl CompressReserveBehavior {
    pub(crate) fn reserve(self, n: usize) -> ReserveResponse {
      match self {
        Self::NewBuf => ReserveResponse::MadeSpace(Vec::with_capacity(n)),
        Self::ExpandBuf(mut buf) => {
          if n > buf.capacity() {
            let additional = n - buf.capacity();
            buf.reserve(additional);
          }
          ReserveResponse::MadeSpace(buf)
        },
        Self::FixedSizeBuf(buf) => {
          if buf.capacity() <= n {
            ReserveResponse::NoSpace(buf)
          } else {
            ReserveResponse::MadeSpace(buf)
          }
        },
      }
    }
  }

  pub struct CompressedStream {
    pub buf: Vec<u8>,
  }

  impl CompressedStream {
    pub fn compress(
      mut into: CompressReserveBehavior,
      live: &LiveStream,
    ) -> Result<Self, CompressionError> {
      let mut required_space: usize = 0;

      /* If we already have an existing buffer to play around with, try that right
       * off to see if it was enough to avoid further allocations. */
      if let Some(ref mut buf) = into.current_buf() {
        match HyperscanRuntimeError::from_native(unsafe {
          hs::hs_compress_stream(
            live.as_ref_native(),
            mem::transmute(buf.as_mut_ptr()),
            buf.capacity(),
            &mut required_space,
          )
        }) {
          Err(HyperscanRuntimeError::InsufficientSpace) => (),
          Err(e) => return Err(e.into()),
          Ok(()) => {
            debug_assert!(buf.capacity() >= required_space);
            unsafe {
              buf.set_len(required_space);
            }
            return Ok(Self {
              buf: mem::take(buf),
            });
          },
        }
      } else {
        /* Otherwise (e.g. if we have a NewBuf), get the required space first
         * before trying to allocate anything by providing
         * NULL for the data pointer. */
        assert_eq!(
          Err(HyperscanRuntimeError::InsufficientSpace),
          HyperscanRuntimeError::from_native(unsafe {
            hs::hs_compress_stream(
              live.as_ref_native(),
              ptr::null_mut(),
              0,
              &mut required_space,
            )
          })
        );
      }
      /* At this point, we know some allocation is necessary, and the
       * `required_space` variable is populated with the amount of space
       * necessary to compress. */

      /* Allocate or fail allocation. */
      let buf = match into.reserve(required_space) {
        ReserveResponse::NoSpace(buf) => {
          /* This is supposed to be what ReserveResponse checks. */
          debug_assert!(required_space > buf.len());
          return Err(CompressionError::NoSpace(required_space, buf));
        },
        ReserveResponse::MadeSpace(mut buf) => {
          let mut allocated_space: usize = 0;
          HyperscanRuntimeError::from_native(unsafe {
            hs::hs_compress_stream(
              live.as_ref_native(),
              mem::transmute(buf.as_mut_ptr()),
              buf.capacity(),
              &mut allocated_space,
            )
          })?;
          /* No particular reason these values should be different across two
           * subsequent calls. */
          debug_assert_eq!(required_space, allocated_space);
          debug_assert!(allocated_space <= buf.capacity());
          unsafe {
            buf.set_len(allocated_space);
          }
          buf
        },
      };

      Ok(Self { buf })
    }

    /* TODO: a .expand_into() method which re-uses the storage of an &mut
     * Streamer argument (similar to .try_clone_from() elsewhere in this file).
     * Would require patching the hyperscan API again to expose a method that
     * separates the "reset" from the "expand into" operation. */
    pub fn expand(&self, db: &Database) -> Result<LiveStream, HyperscanRuntimeError> {
      let mut inner = ptr::null_mut();
      HyperscanRuntimeError::from_native(unsafe {
        hs::hs_expand_stream(
          db.as_ref_native(),
          &mut inner,
          mem::transmute(self.buf.as_ptr()),
          self.buf.len(),
        )
      })?;
      Ok(unsafe { LiveStream::from_native(inner) })
    }
  }
}

/* pub struct StreamSink { */
/* pub live: LiveStream, */
/* scratch: Arc<Scratch>, */
/* matcher: StreamMatcher, */
/* #[allow(clippy::type_complexity)] */
/* write_future: Option<(*const u8, Pin<Box<dyn
 * Future<Output=io::Result<usize>>>>)>, */
/* shutdown_future: Option<Pin<Box<dyn Future<Output=io::Result<()>>>>>, */
/* } */

/* impl StreamSink { */
/* pub fn scan_sync(&mut self, data: ByteSlice) -> Result<(),
 * HyperscanRuntimeError> { */
/* let data_len = data.native_len(); */
/* let data = data.as_ptr() as usize; */
/* let Self { */
/* live, */
/* scratch, */
/* matcher, */
/* .. */
/* } = self; */
/* let p_matcher: *mut StreamMatcher = matcher; */
/* let p_matcher = p_matcher as usize; */
/* HyperscanRuntimeError::from_native(unsafe { */
/* hs::hs_scan_stream( */
/* live.as_mut_native(), */
/* data as *const c_char, */
/* data_len, */
/* /\* NB: ignore flags for now! *\/ */
/* 0, */
/* Arc::make_mut(scratch).as_mut_native().unwrap(), */
/* Some(match_slice_stream), */
/* p_matcher as *mut c_void, */
/* ) */
/* }) */
/* } */

/* pub async fn scan(&mut self, data: ByteSlice<'_>) -> Result<(), ScanError>
 * { */
/* let data: ByteSlice<'static> = unsafe { mem::transmute(data) }; */
/* let s: *mut Self = self; */
/* let s = s as usize; */

/* Ok( */
/* task::spawn_blocking(move || { */
/* let s = unsafe { &mut *(s as *mut Self) }; */
/* s.scan_sync(data) */
/* }) */
/* .await??, */
/* ) */
/* } */

/* pub fn flush_eod_sync(&mut self) -> Result<(), HyperscanRuntimeError> { */
/* let Self { */
/* live, */
/* scratch, */
/* matcher, */
/* .. */
/* } = self; */
/* let p_matcher: *mut StreamMatcher = matcher; */
/* let p_matcher = p_matcher as usize; */
/* HyperscanRuntimeError::from_native(unsafe { */
/* hs::hs_direct_flush_stream( */
/* live.as_mut_native(), */
/* Arc::make_mut(scratch).as_mut_native().unwrap(), */
/* Some(match_slice_stream), */
/* p_matcher as *mut c_void, */
/* ) */
/* }) */
/* } */

/* pub async fn flush_eod(&mut self) -> Result<(), ScanError> { */
/* let s: *mut Self = self; */
/* let s = s as usize; */

/* Ok( */
/* task::spawn_blocking(move || { */
/* let s = unsafe { &mut *(s as *mut Self) }; */
/* s.flush_eod_sync() */
/* }) */
/* .await??, */
/* ) */
/* } */

/* pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> { */
/* let Self { */
/* live, */
/* scratch, */
/* matcher, */
/* .. */
/* } = self; */
/* let live = live.try_clone()?; */
/* let scratch = Arc::clone(scratch); */
/* let matcher = matcher.clone(); */
/* Ok(Self { */
/* live, */
/* scratch, */
/* matcher, */
/* write_future: None, */
/* shutdown_future: None, */
/* }) */
/* } */

/* pub fn try_clone_from(&mut self, source: &Self) -> Result<(),
 * HyperscanRuntimeError> { */
/* let Self { */
/* live, */
/* scratch, */
/* matcher, */
/* .. */
/* } = self; */
/* live.try_clone_from(&source.live)?; */
/* /\* Using Arc::clone_from(): *\/ */
/* scratch.clone_from(&source.scratch); */
/* matcher.clone_from(&source.matcher); */
/* Ok(()) */
/* } */

/* pub fn reset_no_flush(&mut self) -> Result<(), HyperscanRuntimeError> { */
/* self.live.try_reset()?; */
/* self.matcher.handler.reset(); */
/* assert!(self.write_future.is_none()); */
/* assert!(self.shutdown_future.is_none()); */
/* Ok(()) */
/* } */

/* pub fn reset_flush_sync(&mut self) -> Result<(), HyperscanRuntimeError> { */
/* self.flush_eod_sync()?; */
/* self.reset_no_flush()?; */
/* Ok(()) */
/* } */

/* pub async fn reset_flush(&mut self) -> Result<(), ScanError> { */
/* self.flush_eod().await?; */
/* self.reset_no_flush()?; */
/* Ok(()) */
/* } */

/* pub fn compress( */
/* &self, */
/* into: CompressReserveBehavior, */
/* ) -> Result<CompressedStream, CompressionError> { */
/* let Self { */
/* live, */
/* scratch, */
/* matcher, */
/* .. */
/* } = self; */
/* CompressedStream::compress(into, live, Arc::clone(scratch),
 * matcher.clone()) */
/* } */
/* } */

/* impl Clone for StreamSink { */
/* fn clone(&self) -> Self { self.try_clone().unwrap() } */

/* fn clone_from(&mut self, source: &Self) {
 * self.try_clone_from(source).unwrap(); } */
/* } */

/* impl std::io::Write for StreamSink { */
/* fn write(&mut self, buf: &[u8]) -> io::Result<usize> { */
/* self */
/* .scan_sync(ByteSlice::from_slice(buf)) */
/* .map(|_| buf.len()) */
/* .map_err(io::Error::other) */
/* } */

/* fn flush(&mut self) -> io::Result<()> { Ok(()) } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
 * tokio_test::block_on(async { */
/* /// use hyperscan::{expression::*, matchers::*, flags::*, stream::*,
 * error::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// */
/* /// let expr: Expression = "a+".parse()?; */
/* /// let db = expr.compile(Flags::UTF8, Mode::STREAM)?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// struct S(usize); */
/* /// impl StreamScanner for S { */
/* ///   fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult { */
/* ///     if self.0 < 2 { self.0 += 1; MatchResult::Continue } else {
 * MatchResult::CeaseMatching } */
/* ///   } */
/* ///   fn new() -> Self where Self: Sized { Self(0) } */
/* ///   fn reset(&mut self) { self.0 = 0; } */
/* ///   fn boxed_clone(&self) -> Box<dyn StreamScanner> {
 * Box::new(Self(self.0)) } */
/* /// } */
/* /// */
/* /// let mut s = Streamer::open::<S>(&db, scratch.into())?; */
/* /// */
/* /// let msg = "aardvark"; */
/* /// if let Err(e) = s.write_all(msg.as_bytes()).await { */
/* ///   let e = *e.into_inner().unwrap().downcast::<ScanError>().unwrap(); */
/* ///   if let ScanError::ReturnValue(ref e) = e { */
/* ///     assert_eq!(*e, HyperscanRuntimeError::ScanTerminated); */
/* ///   } else { unreachable!(); }; */
/* /// } else { unreachable!(); } */
/* /// s.shutdown().await.unwrap(); */
/* /// let rx = s.stream_results(); */
/* /// */
/* /// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }|
 * &msg[range]).collect().await; */
/* /// // NB: results have no third "aardva" result because of the early
 * CeaseMatching! */
/* /// assert_eq!(results, vec!["a", "aa"]); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub struct Streamer { */
/* pub sink: StreamSink, */
/* pub rx: mpsc::UnboundedReceiver<StreamMatch>, */
/* } */

/* impl Streamer { */
/* pub fn open<S: StreamScanner+'static>( */
/* db: &Database, */
/* scratch: Arc<Scratch>, */
/* ) -> Result<Self, HyperscanRuntimeError> { */
/* let live = LiveStream::try_open(db)?; */

/* let (tx, rx) = mpsc::unbounded_channel(); */
/* let matcher = StreamMatcher::new::<S>(tx); */

/* Ok(Self { */
/* sink: StreamSink { */
/* live, */
/* scratch, */
/* matcher, */
/* write_future: None, */
/* shutdown_future: None, */
/* }, */
/* rx, */
/* }) */
/* } */

/* pub fn scan_sync(&mut self, data: ByteSlice) -> Result<(),
 * HyperscanRuntimeError> { */
/* self.sink.scan_sync(data) */
/* } */

/* pub async fn scan(&mut self, data: ByteSlice<'_>) -> Result<(), ScanError>
 * { */
/* self.sink.scan(data).await */
/* } */

/* pub fn flush_eod_sync(&mut self) -> Result<(), HyperscanRuntimeError> { */
/* self.sink.flush_eod_sync() */
/* } */

/* pub async fn flush_eod(&mut self) -> Result<(), ScanError> {
 * self.sink.flush_eod().await } */

/* pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> { */
/* let mut sink = self.sink.try_clone()?; */

/* let (tx, rx) = mpsc::unbounded_channel(); */
/* sink.matcher.matches_tx = tx; */

/* Ok(Self { sink, rx }) */
/* } */

/* pub fn try_clone_from(&mut self, source: &Self) -> Result<(),
 * HyperscanRuntimeError> { */
/* self.sink.try_clone_from(&source.sink)?; */
/* let _ = self.reset_channel(); */
/* Ok(()) */
/* } */

/* pub fn reset_channel(&mut self) -> impl Stream<Item=StreamMatch> { */
/* let (tx, rx) = mpsc::unbounded_channel(); */
/* self.sink.matcher.matches_tx = tx; */
/* let mut old_rx = mem::replace(&mut self.rx, rx); */
/* old_rx.close(); */
/* UnboundedReceiverStream::new(old_rx) */
/* } */

/* pub fn stream_results(self) -> impl Stream<Item=StreamMatch> { */
/* let Self { mut rx, sink } = self; */
/* mem::drop(sink); */
/* rx.close(); */
/* UnboundedReceiverStream::new(rx) */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
 * tokio_test::block_on(async { */
/* /// use hyperscan::{expression::*, flags::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// */
/* /// let expr: Expression = "a+".parse()?; */
/* /// let db = expr.compile( */
/* ///   Flags::UTF8 | Flags::SOM_LEFTMOST, */
/* ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* /// )?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// let s1 = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */
/* /// */
/* /// let compressed = s1.compress(CompressReserveBehavior::NewBuf)?; */
/* /// std::mem::drop(s1); */
/* /// */
/* /// let msg = "aardvark"; */
/* /// let mut s2 = compressed.expand(&db)?; */
/* /// s2.scan(msg.as_bytes().into()).await?; */
/* /// s2.flush_eod().await?; */
/* /// let rx = s2.stream_results(); */
/* /// */
/* /// let results: Vec<&str> = rx */
/* ///   .map(|StreamMatch { range, .. }| &msg[range]) */
/* ///   .collect() */
/* ///   .await; */
/* /// assert_eq!(results, vec!["a", "aa", "a"]); */
/* /// # Ok(()) */
/* /// # })} */
/* pub fn compress( */
/* &self, */
/* into: CompressReserveBehavior, */
/* ) -> Result<CompressedStream, CompressionError> { */
/* self.sink.compress(into) */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
 * tokio_test::block_on(async { */
/* /// use hyperscan::{expression::*, matchers::*, flags::*, stream::*,
 * error::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// */
/* /// let expr: Literal = "asdf".parse()?; */
/* /// let db = expr.compile(Flags::default(), Mode::STREAM)?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// struct S(usize); */
/* /// impl StreamScanner for S { */
/* ///   fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult { */
/* ///     if self.0 < 2 { self.0 += 1; MatchResult::Continue } else {
 * MatchResult::CeaseMatching } */
/* ///   } */
/* ///   fn new() -> Self where Self: Sized { Self(0) } */
/* ///   fn reset(&mut self) { self.0 = 0; } */
/* ///   fn boxed_clone(&self) -> Box<dyn StreamScanner> {
 * Box::new(Self(self.0)) } */
/* /// } */
/* /// */
/* /// let mut s1 = Streamer::open::<S>(&db, scratch.into())?; */
/* /// */
/* /// s1.write_all(b"asdf").await.unwrap(); */
/* /// let mut s2 = s1.try_clone()?; */
/* /// s1.shutdown().await.unwrap(); */
/* /// let rx1 = s1.stream_results(); */
/* /// s2.write_all(b"asdf").await.unwrap(); */
/* /// s2.reset_no_flush()?; */
/* /// let rx2 = s2.reset_channel(); */
/* /// if let Err(e) = s2.write_all(b"asdfasdfasdf").await { */
/* ///   let e = *e.into_inner().unwrap().downcast::<ScanError>().unwrap(); */
/* ///   if let ScanError::ReturnValue(ref e) = e { */
/* ///     assert_eq!(*e, HyperscanRuntimeError::ScanTerminated); */
/* ///   } else { unreachable!(); } */
/* /// } else { unreachable!(); } */
/* /// s2.shutdown().await.unwrap(); */
/* /// let rx3 = s2.stream_results(); */
/* /// */
/* /// let m1: Vec<_> = rx1.collect().await; */
/* /// let m2: Vec<_> = rx2.collect().await; */
/* /// let m3: Vec<_> = rx3.collect().await; */
/* /// assert_eq!(1, m1.len()); */
/* /// assert_eq!(1, m2.len()); */
/* /// assert_eq!(2, m3.len()); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* /// */
/* /// **TODO: docs** */
/* /// */
/* ///``` */
/* /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
 * tokio_test::block_on(async { */
/* /// use hyperscan::{expression::*, flags::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// */
/* /// let expr: Expression = "asdf$".parse()?; */
/* /// let db = expr.compile(Flags::UTF8, Mode::STREAM)?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// let mut s = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */
/* /// */
/* /// s.write_all(b"asdf").await.unwrap(); */
/* /// s.reset_flush().await?; */
/* /// let rx = s.reset_channel(); */
/* /// s.write_all(b"asdf").await.unwrap(); */
/* /// s.reset_no_flush()?; */
/* /// let rx2 = s.reset_channel(); */
/* /// s.write_all(b"asdf").await.unwrap(); */
/* /// s.shutdown().await.unwrap(); */
/* /// let rx3 = s.stream_results(); */
/* /// */
/* /// let m1: Vec<_> = rx.collect().await; */
/* /// let m2: Vec<_> = rx2.collect().await; */
/* /// let m3: Vec<_> = rx3.collect().await; */
/* /// assert!(!m1.is_empty()); */
/* /// // This will be empty, because .reset_no_flush() was called on sink2 */
/* /// // and the pattern "asdf$" requires matching against the end of data: */
/* /// assert!(m2.is_empty()); */
/* /// assert!(!m3.is_empty()); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub fn reset_no_flush(&mut self) -> Result<(), HyperscanRuntimeError> { */
/* self.sink.reset_no_flush() */
/* } */

/* pub fn reset_flush_sync(&mut self) -> Result<(), HyperscanRuntimeError> { */
/* self.sink.reset_flush_sync() */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
 * tokio_test::block_on(async { */
/* /// use hyperscan::{expression::*, flags::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// use std::ops; */
/* /// */
/* /// let expr: Literal = "asdf".parse()?; */
/* /// let db = expr.compile( */
/* ///   Flags::SOM_LEFTMOST, */
/* ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* /// )?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// let mut s = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */
/* /// */
/* /// s.write_all(b"asdf..").await.unwrap(); */
/* /// let rx = s.reset_channel(); */
/* /// s.reset_flush().await?; */
/* /// s.write_all(b"..asdf").await.unwrap(); */
/* /// s.shutdown().await.unwrap(); */
/* /// let rx2 = s.stream_results(); */
/* /// */
/* /// let m1: Vec<ops::Range<usize>> = rx.map(|m| m.range).collect().await; */
/* /// let m2: Vec<ops::Range<usize>> = rx2.map(|m| m.range).collect().await; */
/* /// // The stream state should have been reset, so rx2 should have
 * restarted the stream offset */
/* /// // from the beginning: */
/* /// assert_eq!(m1, vec![0..4]); */
/* /// assert_eq!(m2, vec![2..6]); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub async fn reset_flush(&mut self) -> Result<(), ScanError> {
 * self.sink.reset_flush().await } */

/* fn sink_pin(self: Pin<&mut Self>) -> Pin<&mut StreamSink> { */
/* unsafe { self.map_unchecked_mut(|s| &mut s.sink) } */
/* } */
/* } */

/* impl Clone for Streamer { */
/* fn clone(&self) -> Self { self.try_clone().unwrap() } */

/* fn clone_from(&mut self, source: &Self) {
 * self.try_clone_from(source).unwrap(); } */
/* } */

/* impl std::io::Write for Streamer { */
/* fn write(&mut self, buf: &[u8]) -> io::Result<usize> { */
/* self */
/* .scan_sync(ByteSlice::from_slice(buf)) */
/* .map(|_| buf.len()) */
/* .map_err(io::Error::other) */
/* } */

/* fn flush(&mut self) -> io::Result<()> { Ok(()) } */
/* } */

/* impl AsyncWrite for Streamer { */
/* fn poll_write(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) ->
 * Poll<io::Result<usize>> { */
/* self.sink_pin().poll_write(cx, buf) */
/* } */

/* fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) ->
 * Poll<io::Result<()>> { */
/* self.sink_pin().poll_flush(cx) */
/* } */

/* fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) ->
 * Poll<io::Result<()>> { */
/* self.sink_pin().poll_shutdown(cx) */
/* } */
/* } */

/* pub struct CompressedStream { */
/* pub buf: Vec<u8>, */
/* scratch: Arc<Scratch>, */
/* matcher: StreamMatcher, */
/* } */

/* impl CompressedStream { */
/* pub(crate) fn compress( */
/* into: CompressReserveBehavior, */
/* live: &LiveStream, */
/* scratch: Arc<Scratch>, */
/* matcher: StreamMatcher, */
/* ) -> Result<Self, CompressionError> { */
/* let mut required_space = mem::MaybeUninit::<usize>::zeroed(); */
/* assert_eq!( */
/* Err(HyperscanRuntimeError::InsufficientSpace), */
/* HyperscanRuntimeError::from_native(unsafe { */
/* hs::hs_compress_stream( */
/* (*live).as_ref_native(), */
/* ptr::null_mut(), */
/* 0, */
/* required_space.as_mut_ptr(), */
/* ) */
/* }) */
/* ); */
/* let mut required_space = unsafe { required_space.assume_init() }; */

/* let buf = match into.reserve(required_space) { */
/* ReserveResponse::NoSpace(_) => return
 * Err(CompressionError::NoSpace(required_space)), */
/* ReserveResponse::MadeSpace(mut buf) => { */
/* HyperscanRuntimeError::from_native(unsafe { */
/* hs::hs_compress_stream( */
/* live.as_ref_native(), */
/* mem::transmute(buf.as_mut_ptr()), */
/* required_space, */
/* &mut required_space, */
/* ) */
/* })?; */
/* buf */
/* }, */
/* }; */

/* Ok(Self { */
/* buf, */
/* scratch, */
/* matcher, */
/* }) */
/* } */

/* /\* TODO: a .expand_into() method which re-uses the storage of an &mut */
/* * Streamer argument (similar to .try_clone_from() elsewhere in this file). */
/* * Would require patching the hyperscan API again to expose a method that */
/* * separates the "reset" from the "expand into" operation. *\/ */
/* pub fn expand(&self, db: &Database) -> Result<Streamer,
 * HyperscanRuntimeError> { */
/* let mut inner = ptr::null_mut(); */
/* HyperscanRuntimeError::from_native(unsafe { */
/* hs::hs_expand_stream( */
/* db.as_ref_native(), */
/* &mut inner, */
/* mem::transmute(self.buf.as_ptr()), */
/* self.buf.capacity(), */
/* ) */
/* })?; */
/* let live = unsafe { LiveStream::from_native(inner) }; */

/* let mut matcher = self.matcher.clone(); */
/* let (tx, rx) = mpsc::unbounded_channel(); */
/* matcher.matches_tx = tx; */

/* let sink = StreamSink { */
/* live, */
/* scratch: self.scratch.clone(), */
/* matcher, */
/* write_future: None, */
/* shutdown_future: None, */
/* }; */
/* Ok(Streamer { sink, rx }) */
/* } */
/* } */

/* #[cfg(all(test, feature = "compiler"))] */
/* mod test { */
/* use super::*; */
/* use crate::{ */
/* expression::Expression, */
/* flags::{Flags, Mode}, */
/* }; */

/* use futures_util::StreamExt; */

/* use std::{mem, sync::Arc}; */

/* #[tokio::test] */
/* async fn clone_scratch() -> Result<(), eyre::Report> { */
/* let expr: Expression = "asdf$".parse()?; */
/* let db = expr.compile(Flags::UTF8, Mode::STREAM)?; */

/* let scratch = Arc::new(db.allocate_scratch()?); */
/* let s2 = Arc::clone(&scratch); */

/* let msg = "asdf"; */
/* let mut s = Streamer::open::<TrivialScanner>(&db, s2)?; */
/* mem::drop(scratch); */
/* s.scan(msg.into()).await?; */
/* s.flush_eod().await?; */
/* let rx = s.stream_results(); */

/* let results: Vec<&str> = rx.map(|m| &msg[m.range]).collect().await; */
/* assert_eq!(&results, &["asdf"]); */
/* Ok(()) */
/* } */

/* #[tokio::test] */
/* async fn compress() -> Result<(), eyre::Report> { */
/* let expr: Expression = "a+".parse()?; */
/* let db = expr.compile( */
/* Flags::UTF8 | Flags::SOM_LEFTMOST, */
/* Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* )?; */
/* let scratch = db.allocate_scratch()?; */

/* let s1 = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */

/* let compressed = s1.compress(CompressReserveBehavior::NewBuf)?; */
/* mem::drop(s1); */

/* let msg = "aardvark"; */
/* let mut s2 = compressed.expand(&db)?; */
/* s2.scan(msg.as_bytes().into()).await?; */
/* s2.flush_eod().await?; */
/* let rx = s2.stream_results(); */

/* let results: Vec<&str> = rx */
/* .map(|StreamMatch { range, .. }| &msg[range]) */
/* .collect() */
/* .await; */
/* assert_eq!(results, vec!["a", "aa", "a"]); */
/* Ok(()) */
/* } */
/* } */

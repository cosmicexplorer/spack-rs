/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  database::Database,
  error::{CompressionError, HyperscanRuntimeError},
  handle::{Handle, Resource},
  hs,
  matchers::stream::StreamMatcher,
  sources::ByteSlice,
  state::Scratch,
};

use std::{mem, ops, ptr};

pub type NativeStream = hs::hs_stream;

#[derive(Debug)]
#[repr(transparent)]
pub struct LiveStream(*mut NativeStream);

unsafe impl Send for LiveStream {}
unsafe impl Sync for LiveStream {}

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

  /// # Safety
  /// `self` and `source` must have been opened against the same db!
  pub unsafe fn try_clone_from(&mut self, source: &Self) -> Result<(), HyperscanRuntimeError> {
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

/// NB: [`Clone::clone_from()`] is not implemented because
/// [`Self::try_clone_from()`] is unsafe!
impl Clone for LiveStream {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl Resource for LiveStream {
  type Error = HyperscanRuntimeError;

  fn deep_clone(&self) -> Result<Self, Self::Error> { self.try_clone() }

  fn deep_boxed_clone(&self) -> Result<Box<dyn Resource<Error=Self::Error>>, Self::Error> {
    Ok(Box::new(self.try_clone()?))
  }

  unsafe fn sync_drop(&mut self) -> Result<(), Self::Error> { self.try_drop() }
}

impl ops::Drop for LiveStream {
  fn drop(&mut self) {
    unsafe {
      self.try_drop().unwrap();
    }
  }
}

/* TODO: update ScratchInUse flag docs to point to state/handle module docs! */
pub struct StreamSink<'code> {
  pub live: Box<dyn Handle<R=LiveStream>+'code>,
  pub matcher: StreamMatcher<'code>,
}

impl<'code> StreamSink<'code> {
  pub fn new(live: impl Handle<R=LiveStream>+'code, matcher: StreamMatcher<'code>) -> Self {
    Self {
      live: Box::new(live),
      matcher,
    }
  }

  pub fn scan<'data>(
    &mut self,
    scratch: &mut Scratch,
    data: ByteSlice<'data>,
  ) -> Result<(), HyperscanRuntimeError> {
    let Self { live, matcher } = self;
    scratch.scan_sync_stream(live.make_mut()?, matcher, data)
  }

  pub fn flush_eod(&mut self, scratch: &mut Scratch) -> Result<(), HyperscanRuntimeError> {
    let Self { live, matcher } = self;
    scratch.flush_eod_sync(live.make_mut()?, matcher)
  }

  pub fn reset(&mut self) -> Result<(), HyperscanRuntimeError> { self.live.make_mut()?.try_reset() }
}

///```
/// #[cfg(feature = "compiler")]
/// fn main() -> Result<(), hyperscan::error::HyperscanError> {
///   use hyperscan::{expression::*, flags::*, stream::*, matchers::{*, stream::*}};
///   use std::{ops::Range, mem};
///
///   let expr: Expression = "a+".parse()?;
///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
///   let scratch = db.allocate_scratch()?;
///   let live = db.allocate_stream()?;
///
///   // Create the `matches` vector which is mutably captured in the dyn closure.
///   let mut matches: Vec<StreamMatch> = Vec::new();
///   // Capture `matches` into `match_fn`;
///   // in this case, `match_fn` is an unboxed stack-allocated closure.
///   let mut match_fn = |m| {
///     matches.push(m);
///     MatchResult::Continue
///   };
///   // `matcher` now keeps the reference to `matches` alive
///   // in rustc's local lifetime tracking.
///   let matcher = StreamMatcher::new(&mut match_fn);
///   let sink = StreamSink::new(live, matcher);
///   let mut sink = ScratchStreamSink::new(sink, scratch);
///
///   sink.scan("aardvark".into())?;
///   sink.flush_eod()?;
///
///   // This will also drop `matcher`, which means `match_fn`
///   // holds the only reference to `matches`.
///   mem::drop(sink);
///   // This could also be performed by explicitly
///   // introducing a scope with `{}`.
///
///   // Since `match_fn` is otherwise unused outside of `matcher`,
///   // rustc can statically determine that no other mutable reference
///   // to `matches` exists, so it "unlocks" the value
///   // and lets us consume it with `.into_iter()`.
///   let matches: Vec<Range<usize>> = matches
///     .into_iter()
///     .map(|m| m.range.into())
///     .collect();
///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
///   Ok(())
/// }
/// # #[cfg(not(feature = "compiler"))]
/// # fn main() {}
/// ```
pub struct ScratchStreamSink<'code> {
  pub sink: StreamSink<'code>,
  pub scratch: Box<dyn Handle<R=Scratch>+'code>,
}

impl<'code> ScratchStreamSink<'code> {
  pub fn new(sink: StreamSink<'code>, scratch: impl Handle<R=Scratch>+'code) -> Self {
    Self {
      sink,
      scratch: Box::new(scratch),
    }
  }

  pub fn scan<'data>(&mut self, data: ByteSlice<'data>) -> Result<(), HyperscanRuntimeError> {
    let Self { sink, scratch } = self;
    sink.scan(scratch.make_mut()?, data)
  }

  pub fn flush_eod(&mut self) -> Result<(), HyperscanRuntimeError> {
    let Self { sink, scratch } = self;
    sink.flush_eod(scratch.make_mut()?)
  }
}

impl<'code> std::io::Write for ScratchStreamSink<'code> {
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
  use super::LiveStream;
  use crate::{
    error::{HyperscanRuntimeError, ScanError},
    handle::Handle,
    matchers::{
      stream::{SendStreamMatcher, StreamMatch},
      MatchResult,
    },
    sources::ByteSlice,
    state::Scratch,
  };

  use futures_core::stream::Stream;
  use tokio::{sync::mpsc, task};

  use std::mem;

  pub struct StreamSinkChannel<'code> {
    pub live: Box<dyn Handle<R=LiveStream>+Send+'code>,
    pub hf: Box<dyn FnMut(StreamMatch) -> MatchResult+Send+'code>,
    pub rx: mpsc::UnboundedReceiver<StreamMatch>,
  }

  impl<'code> StreamSinkChannel<'code> {
    fn translate_async_sender(
      hf: &'code mut (dyn FnMut(&StreamMatch) -> MatchResult+Send+'code),
      tx: mpsc::UnboundedSender<StreamMatch>,
    ) -> Box<dyn FnMut(StreamMatch) -> MatchResult+Send+'code> {
      Box::new(move |m| {
        let result = hf(&m);
        tx.send(m).unwrap();
        result
      })
    }

    pub fn new(
      live: impl Handle<R=LiveStream>+Send+'code,
      hf: &'code mut (dyn FnMut(&StreamMatch) -> MatchResult+Send+'code),
    ) -> Self {
      let (tx, rx) = mpsc::unbounded_channel();
      let hf = Self::translate_async_sender(hf, tx);
      Self {
        live: Box::new(live),
        hf,
        rx,
      }
    }

    pub async fn scan<'data>(
      &mut self,
      scratch: &mut Scratch,
      data: ByteSlice<'data>,
    ) -> Result<(), ScanError> {
      /* Make the mutable resources static. */
      let Self { live, hf, .. } = self;
      let live: &'static mut LiveStream = unsafe { mem::transmute(live.make_mut()?) };
      let scratch: &'static mut Scratch = unsafe { mem::transmute(scratch) };
      let data: ByteSlice<'static> = unsafe { mem::transmute(data) };

      /* Generate a vtable pointing to the heap-allocated handler function hf. */
      let hf: &mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code) = hf;
      let matcher = SendStreamMatcher::new(hf);
      let mut matcher: SendStreamMatcher<'static> = unsafe { mem::transmute(matcher) };

      task::spawn_blocking(move || scratch.scan_sync_stream(live, matcher.as_mut_basic(), data))
        .await??;
      Ok(())
    }

    pub async fn flush_eod(&mut self, scratch: &mut Scratch) -> Result<(), ScanError> {
      /* Make the mutable resources static. */
      let Self { live, hf, .. } = self;
      let live: &'static mut LiveStream = unsafe { mem::transmute(live.make_mut()?) };
      let scratch: &'static mut Scratch = unsafe { mem::transmute(scratch) };

      /* Generate a vtable pointing to the heap-allocated handler function hf. */
      let hf: &mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code) = hf;
      let matcher = SendStreamMatcher::new(hf);
      let mut matcher: SendStreamMatcher<'static> = unsafe { mem::transmute(matcher) };

      task::spawn_blocking(move || {
        scratch.flush_eod_sync(live.make_mut()?, matcher.as_mut_basic())
      })
      .await??;
      Ok(())
    }

    pub fn collect_matches(mut self) -> impl Stream<Item=StreamMatch> {
      self.rx.close();
      crate::async_utils::UnboundedReceiverStream(self.rx)
    }

    pub fn reset(&mut self) -> Result<(), HyperscanRuntimeError> {
      self.live.make_mut()?.try_reset()
    }
  }

  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  ///   use hyperscan::{expression::*, flags::*, stream::channel::*, matchers::*};
  ///   use futures_util::StreamExt;
  ///   use std::ops::Range;
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
  ///   let scratch = db.allocate_scratch()?;
  ///   let live = db.allocate_stream()?;
  ///
  ///   let mut match_fn = |_: &_| MatchResult::Continue;
  ///   let sink = StreamSinkChannel::new(live, &mut match_fn);
  ///   let mut sink = ScratchStreamSinkChannel::new(sink, scratch);
  ///
  ///   sink.scan("aardvark".into()).await?;
  ///   sink.flush_eod().await?;
  ///
  ///   let matches: Vec<Range<usize>> = sink.sink.collect_matches()
  ///     .map(|m| m.range.into())
  ///     .collect()
  ///     .await;
  ///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
  ///   Ok(())
  /// })}
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub struct ScratchStreamSinkChannel<'code> {
    pub sink: StreamSinkChannel<'code>,
    pub scratch: Box<dyn Handle<R=Scratch>+Send+'code>,
  }

  impl<'code> ScratchStreamSinkChannel<'code> {
    pub fn new(sink: StreamSinkChannel<'code>, scratch: impl Handle<R=Scratch>+Send+'code) -> Self {
      Self {
        sink,
        scratch: Box::new(scratch),
      }
    }

    pub async fn scan<'data>(&mut self, data: ByteSlice<'data>) -> Result<(), ScanError> {
      let Self { sink, scratch, .. } = self;
      sink.scan(scratch.make_mut()?, data).await
    }

    pub async fn flush_eod(&mut self) -> Result<(), ScanError> {
      let Self { sink, scratch, .. } = self;
      sink.flush_eod(scratch.make_mut()?).await
    }
  }

  #[cfg(feature = "tokio-impls")]
  #[cfg_attr(docsrs, doc(cfg(feature = "tokio-impls")))]
  pub mod tokio_impls {
    use super::ScratchStreamSinkChannel;
    use crate::sources::ByteSlice;

    use futures_util::TryFutureExt;
    use tokio::io;

    use std::{
      future::Future,
      pin::Pin,
      slice,
      task::{ready, Context, Poll},
    };

    ///```
    /// #[cfg(feature = "compiler")]
    /// fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
    ///   use hyperscan::{expression::*, flags::*, stream::channel::{*, tokio_impls::*}, matchers::*};
    ///   use futures_util::StreamExt;
    ///   use tokio::io::AsyncWriteExt;
    ///   use std::ops::Range;
    ///
    ///   let expr: Expression = "a+".parse()?;
    ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
    ///   let scratch = db.allocate_scratch()?;
    ///   let live = db.allocate_stream()?;
    ///
    ///   let mut match_fn = |_: &_| MatchResult::Continue;
    ///   let sink = StreamSinkChannel::new(live, &mut match_fn);
    ///   let sink = ScratchStreamSinkChannel::new(sink, scratch);
    ///   let mut sink = StreamWriter::new(sink);
    ///
    ///   sink.write_all(b"aardvark").await.unwrap();
    ///   sink.shutdown().await.unwrap();
    ///
    ///   let matches: Vec<Range<usize>> = sink.inner.sink.collect_matches()
    ///     .map(|m| m.range.into())
    ///     .collect()
    ///     .await;
    ///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
    ///   Ok(())
    /// })}
    /// # #[cfg(not(feature = "compiler"))]
    /// # fn main() {}
    /// ```
    pub struct StreamWriter<'code> {
      pub inner: ScratchStreamSinkChannel<'code>,
      #[allow(clippy::type_complexity)]
      write_future: Option<(
        *const u8,
        Pin<Box<dyn Future<Output=io::Result<usize>>+'code>>,
      )>,
      shutdown_future: Option<Pin<Box<dyn Future<Output=io::Result<()>>+'code>>>,
    }

    impl<'code> StreamWriter<'code> {
      pub fn new(inner: ScratchStreamSinkChannel<'code>) -> Self {
        Self {
          inner,
          write_future: None,
          shutdown_future: None,
        }
      }
    }

    unsafe impl<'code> Send for StreamWriter<'code> {}

    impl<'code> io::AsyncWrite for StreamWriter<'code> {
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
              .inner
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
          let mut fut: Pin<Box<dyn Future<Output=io::Result<()>>>> = Box::pin(
            unsafe { &mut *s }
              .inner
              .flush_eod()
              .map_err(io::Error::other),
          );

          if let Poll::Ready(ret) = fut.as_mut().poll(cx) {
            return Poll::Ready(ret);
          }

          self.shutdown_future = Some(fut);

          Poll::Pending
        }
      }

      /* TODO: add vectored write support if vectored streaming databases
      ever
      * exist! */
    }
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

  enum ReserveResponse {
    MadeSpace(Vec<u8>),
    NoSpace(Vec<u8>),
  }

  impl CompressReserveBehavior {
    fn reserve(self, n: usize) -> ReserveResponse {
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

    /// # Safety
    /// `self` and `to` must have been opened against the same db!
    pub unsafe fn expand_into(&self, to: &mut LiveStream) -> Result<(), HyperscanRuntimeError> {
      HyperscanRuntimeError::from_native(hs::hs_direct_expand_into(
        to.as_mut_native(),
        mem::transmute(self.buf.as_ptr()),
        self.buf.len(),
      ))?;
      Ok(())
    }
  }
}

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

/* let live = LiveStream::try_open(&db)?; */

/* let scratch = Arc::new(db.allocate_scratch()?; */
/* let s2 = Arc::clone(&scratch); */

/* let msg = "asdf"; */
/* let mut s = StreamSinkChannel::new::<TrivialScanner>(&db, s2)?; */
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

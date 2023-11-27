/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  database::Database,
  error::HyperscanError,
  flags::ScanFlags,
  hs,
  matchers::{ByteSlice, ExpressionIndex, MatchEvent, MatchResult},
  state::Scratch,
};

use futures_util::pin_mut;
use tokio::{
  io::{self, AsyncWrite},
  sync::mpsc,
  task,
};

use std::{
  future::Future,
  ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
  task::{Context, Poll},
};

///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
/// use hyperscan::{expression::*, flags::*, state::*, stream::*};
/// use futures_util::StreamExt;
///
/// let expr: Expression = r"\b\w+\b".parse()?;
/// let db = expr.compile(
///   Flags::UTF8 | Flags::SOM_LEFTMOST,
///   Mode::STREAM | Mode::SOM_HORIZON_LARGE,
/// )?;
///
/// let flags = ScanFlags::default();
/// let Streamer { mut sink, rx } = Streamer::try_open((flags, &db, 32)).await?;
/// let rx = tokio_stream::wrappers::ReceiverStream::new(rx);
///
/// let msg1 = "aardvark ";
/// sink.scan(msg1.as_bytes().into(), flags).await?;
///
/// let msg2 = "asdf was a friend ";
/// sink.scan(msg2.as_bytes().into(), flags).await?;
///
/// let msg3 = "after all";
/// sink.scan(msg3.as_bytes().into(), flags).await?;
/// sink.try_drop().await?;
/// std::mem::drop(sink);
///
/// let msgs: String = [msg1, msg2, msg3].concat();
/// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }| &msgs[range]).collect().await;
/// assert_eq!(results, vec![
///   "aardvark",
///   "asdf",
///   "was",
///   "a",
///   "friend",
///   "after",
///   "all",
/// ]);
/// # Ok(())
/// # })}
/// ```
#[derive(Debug)]
pub struct StreamMatch {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
}

pub trait StreamScanner {
  fn stream_scan(&mut self, m: &StreamMatch) -> MatchResult;

  fn new() -> Self
  where Self: Sized;

  fn reset(&mut self);
  fn boxed_clone(&self) -> Box<dyn StreamScanner>;
}

pub(crate) struct StreamMatcher {
  pub matches_tx: mpsc::Sender<StreamMatch>,
  pub handler: Box<dyn StreamScanner>,
}

impl StreamMatcher {
  pub fn new<S: StreamScanner+'static>(matches_tx: mpsc::Sender<StreamMatch>) -> Self {
    Self {
      matches_tx,
      handler: Box::new(S::new()),
    }
  }

  #[inline(always)]
  pub fn push_new_match(&mut self, m: StreamMatch) { self.matches_tx.blocking_send(m).unwrap(); }

  #[inline(always)]
  pub fn handle_match(&mut self, m: &StreamMatch) -> MatchResult { (self.handler).stream_scan(m) }
}

impl Clone for StreamMatcher {
  fn clone(&self) -> Self {
    Self {
      matches_tx: self.matches_tx.clone(),
      handler: self.handler.boxed_clone(),
    }
  }
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
    context,
    /* NB: ignore flags for now! */
    ..
  } = MatchEvent::coerce_args(id, from, to, flags, context);
  let mut matcher: Pin<&mut StreamMatcher> =
    MatchEvent::extract_context::<'_, StreamMatcher>(context).unwrap();

  let m = StreamMatch { id, range };

  let result = matcher.handle_match(&m);
  if result == MatchResult::Continue {
    matcher.push_new_match(m);
  }

  result.into_native()
}

#[derive(Debug)]
#[repr(transparent)]
pub struct LiveStream(*mut hs::hs_stream);

unsafe impl Send for LiveStream {}
unsafe impl Sync for LiveStream {}

impl LiveStream {
  #[inline]
  pub(crate) const unsafe fn from_native(p: *mut hs::hs_stream) -> Self { Self(p) }

  #[inline]
  pub(crate) const fn as_ref_native(&self) -> &hs::hs_stream { unsafe { &*self.0 } }

  #[inline]
  pub(crate) const fn as_mut_native(&mut self) -> &mut hs::hs_stream { unsafe { &mut *self.0 } }

  pub fn try_open(db: &Database) -> Result<Self, HyperscanError> {
    let mut ret = ptr::null_mut();
    HyperscanError::from_native(unsafe {
      hs::hs_open_stream(
        db.as_ref_native(),
        /* NB: ignoring flags for now! */
        ScanFlags::default().into_native(),
        &mut ret,
      )
    })?;
    Ok(unsafe { Self::from_native(ret) })
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanError> {
    let mut ret = ptr::null_mut();
    HyperscanError::from_native(unsafe { hs::hs_copy_stream(&mut ret, self.as_ref_native()) })?;
    Ok(unsafe { Self::from_native(ret) })
  }

  pub fn try_clone_from(&mut self, source: &Self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_direct_reset_and_copy_stream(self.as_mut_native(), source.as_ref_native())
    })
  }

  pub unsafe fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_direct_free_stream(self.as_mut_native()) })
  }

  pub fn try_reset(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_direct_reset_stream(self.as_mut_native()) })
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
  live: LiveStream,
  scratch: Scratch,
  matcher: StreamMatcher,
}

impl AsyncWrite for StreamSink {
  fn poll_write(self: Pin<&mut Self>, cx: &mut Context<'_>, buf: &[u8]) -> Poll<io::Result<usize>> {
    let fut = self.get_mut().scan(ByteSlice::from_slice(buf));
    pin_mut!(fut);
    fut
      .poll(cx)
      .map_ok(|()| buf.len())
      .map_err(|e| io::Error::new(io::ErrorKind::Other, e))
  }

  fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
    Poll::Ready(Ok(()))
  }

  fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
    let fut = self.get_mut().flush_eod();
    pin_mut!(fut);
    fut
      .poll(cx)
      .map_err(|e| io::Error::new(io::ErrorKind::Other, e))
  }

  /* TODO: add vectored write support if vectored streaming databases ever exist! */
}

impl StreamSink {
  pub async fn scan(&mut self, data: ByteSlice<'_>) -> Result<(), HyperscanError> {
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
      let p_matcher: *mut StreamMatcher = matcher;
      let p_matcher = p_matcher as usize;
      HyperscanError::from_native(unsafe {
        hs::hs_scan_stream(
          live.as_mut_native(),
          data as *const c_char,
          data_len,
          /* NB: ignore flags for now! */
          ScanFlags::default().into_native(),
          scratch.as_mut_native().unwrap(),
          Some(match_slice_stream),
          p_matcher as *mut c_void,
        )
      })
    })
    .await
    .unwrap()
  }

  pub async fn flush_eod(&mut self) -> Result<(), HyperscanError> {
    let s: *mut Self = self;
    let s = s as usize;

    task::spawn_blocking(move || {
      let Self {
        live,
        scratch,
        matcher,
      } = unsafe { &mut *(s as *mut Self) };
      let p_matcher: *mut StreamMatcher = matcher;
      let p_matcher = p_matcher as usize;
      HyperscanError::from_native(unsafe {
        hs::hs_direct_flush_stream(
          live.as_mut_native(),
          scratch.as_mut_native().unwrap(),
          Some(match_slice_stream),
          p_matcher as *mut c_void,
        )
      })
    })
    .await
    .unwrap()
  }
}

/* impl<'db, S: Send+Sync> StreamSink<'db, S> { */
/* ///``` */
/* /// # fn main() -> Result<(), eyre::Report> { tokio_test::block_on(async { */
/* /// use hyperscan::{expression::*, flags::*, state::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// */
/* /// let expr: Expression = "a+".parse()?; */
/* /// let db = expr.compile( */
/* ///   Flags::UTF8 | Flags::SOM_LEFTMOST, */
/* ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* /// )?; */
/* /// */
/* /// let flags = ScanFlags::default(); */
/* /// let Streamer { mut sink, mut rx } = Streamer::try_open((flags, &db,
 * 32)).await?; */
/* /// */
/* /// let buf = sink.compress(CompressReserveBehavior::NewBuf).await?; */
/* /// sink.try_drop().await?; */
/* /// std::mem::drop(sink); */
/* /// */
/* /// let msg = "aardvark"; */
/* /// let mut sink = buf.expand().await?; */
/* /// sink.scan(msg.as_bytes().into(), flags).await?; */
/* /// sink.try_drop().await?; */
/* /// std::mem::drop(sink); */
/* /// */
/* /// // Although there are further senders in Arc shared pointers, */
/* /// // we cut them off here in order to ensure our stream terminates. */
/* /// rx.close(); */
/* /// let rx = tokio_stream::wrappers::ReceiverStream::new(rx); */
/* /// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }|
 * &msg[range]).collect().await; */
/* /// assert_eq!(results, vec!["a", "aa", "a"]); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub async fn compress( */
/* &self, */
/* into: CompressReserveBehavior, */
/* ) -> Result<CompressedStream<'db, S>, CompressionError> { */
/* let Self { */
/* live, */
/* flags, */
/* scratch, */
/* matcher, */
/* } = self; */
/* CompressedStream::compress(into, live, *flags, scratch, matcher).await */
/* } */
/* } */

///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
/// use hyperscan::{expression::*, flags::*, state::*, stream::*};
/// use futures_util::StreamExt;
///
/// let expr: Expression = "a+".parse()?;
/// let db = expr.compile(Flags::UTF8, Mode::STREAM)?;
///
/// let flags = ScanFlags::default();
/// let Streamer { mut sink, rx } = Streamer::try_open((flags, &db, 32)).await?;
/// let rx = tokio_stream::wrappers::ReceiverStream::new(rx);
///
/// let msg = "aardvark";
/// sink.scan(msg.as_bytes().into(), flags).await?;
/// sink.try_drop().await?;
/// std::mem::drop(sink);
///
/// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }| &msg[range]).collect().await;
/// assert_eq!(results, vec!["a", "aa", "aardva"]);
///
/// # Ok(())
/// # })}
/// ```
pub struct Streamer {
  pub sink: StreamSink,
  pub rx: mpsc::Receiver<StreamMatch>,
}

impl Streamer {
  pub fn new<S: StreamScanner+'static>(
    db: &Database,
    scratch: Scratch,
    channel_size: usize,
  ) -> Result<Self, HyperscanError> {
    let live = LiveStream::try_open(db)?;

    let (tx, rx) = mpsc::channel(channel_size);
    let matcher = StreamMatcher::new::<S>(tx);

    Ok(Self {
      sink: StreamSink {
        live,
        scratch,
        matcher,
      },
      rx,
    })
  }

  pub async fn reset(&mut self, channel_size: usize) -> Result<(), HyperscanError> {
    self.sink.flush_eod().await?;
    self.sink.live.try_reset()?;
    self.sink.matcher.handler.reset();

    let (tx, rx) = mpsc::channel(channel_size);
    self.sink.matcher.matches_tx = tx;
    self.rx = rx;

    Ok(())
  }
}

/* pub struct CompressedStream<S> { */
/* pub buf: Vec<c_char>, */
/* pub flags: ScanFlags, */
/* pub scratch: Arc<Scratch>, */
/* pub matcher: Arc<StreamMatcher<S>>, */
/* } */

/* impl<S: Send+Sync> CompressedStream<S> { */
/* pub(crate) async fn compress<'db>( */
/* into: CompressReserveBehavior, */
/* live: &LiveStream<'db>, */
/* flags: ScanFlags, */
/* scratch: &Arc<Scratch>, */
/* matcher: &Arc<StreamMatcher<S>>, */
/* ) -> Result<Self, CompressionError> { */
/* let live: *const LiveStream<'db> = live; */
/* let live = live as usize; */

/* let buf = task::spawn_blocking(move || { */
/* let live: *const LiveStream<'db> = unsafe { &*(live as *const
 * LiveStream<'db>) }; */

/* let mut required_space = mem::MaybeUninit::<usize>::zeroed(); */
/* assert_eq!( */
/* Err(HyperscanError::InsufficientSpace), */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_compress_stream( */
/* (*live).as_ref_native(), */
/* ptr::null_mut(), */
/* 0, */
/* required_space.as_mut_ptr(), */
/* ) */
/* }) */
/* ); */
/* let mut required_space = unsafe { required_space.assume_init() }; */

/* match into.reserve(required_space) { */
/* ReserveResponse::NoSpace(_) =>
 * Err(CompressionError::NoSpace(required_space)), */
/* ReserveResponse::MadeSpace(mut buf) => { */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_compress_stream( */
/* (*live).as_ref_native(), */
/* buf.as_mut_ptr(), */
/* required_space, */
/* &mut required_space, */
/* ) */
/* })?; */
/* Ok(buf) */
/* }, */
/* } */
/* }) */
/* .await */
/* .unwrap()?; */

/* Ok(Self { */
/* buf, */
/* flags, */
/* scratch: scratch.clone(), */
/* matcher: matcher.clone(), */
/* }) */
/* } */

/* pub async fn expand(&self) -> Result<StreamSink<'db, S>, HyperscanError> { */
/* let s: *const Self = self; */
/* let s = s as usize; */

/* let (inner, flags) = task::spawn_blocking(move || { */
/* let Self { */
/* scratch, */
/* buf, */
/* flags, */
/* .. */
/* } = unsafe { &*(s as *const Self) }; */
/* let mut inner = ptr::null_mut(); */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_expand_stream( */
/* scratch.db_ref_native().get_ref(), */
/* &mut inner, */
/* buf.as_ptr(), */
/* buf.capacity(), */
/* ) */
/* })?; */
/* Ok::<_, HyperscanError>((inner as usize, *flags)) */
/* }) */
/* .await */
/* .unwrap()?; */

/* let live = LiveStream { */
/* inner: inner as *mut hs::hs_stream, */
/* _ph: PhantomData, */
/* }; */
/* Ok(StreamSink { */
/* live, */
/* flags, */
/* scratch: self.scratch.clone(), */
/* matcher: self.matcher.clone(), */
/* }) */
/* } */
/* } */

/* impl<'db> CompressedStream<'db, AcceptMatches> { */
/* pub async fn expand_and_reset(&self) -> Result<StreamSink<'db,
 * AcceptMatches>, HyperscanError> { */
/* let s: *const Self = self; */
/* let s = s as usize; */

/* let mut scratch = self.scratch.clone(); */
/* let p_scratch: *mut hs::hs_scratch = Arc::make_mut(&mut
 * scratch).as_mut_native(); */
/* let p_scratch = p_scratch as usize; */

/* let mut matcher = self.matcher.clone(); */
/* let p_matcher: *mut StreamMatcher<AcceptMatches> = Arc::make_mut(&mut
 * matcher); */
/* let p_matcher_n = p_matcher as usize; */

/* let (inner, flags) = task::spawn_blocking(move || { */
/* let Self { buf, flags, .. } = unsafe { &*(s as *const Self) }; */

/* let mut stream = mem::MaybeUninit::<hs::hs_stream>::uninit(); */
/* HyperscanError::from_native(unsafe { */
/* hs::hs_reset_and_expand_stream( */
/* stream.as_mut_ptr(), */
/* buf.as_ptr(), */
/* buf.capacity(), */
/* p_scratch as *mut hs::hs_scratch, */
/* Some(match_slice_stream), */
/* p_matcher_n as *mut c_void, */
/* ) */
/* })?; */
/* Ok::<_, HyperscanError>((stream.as_mut_ptr() as usize, *flags)) */
/* }) */
/* .await */
/* .unwrap()?; */

/* let live = LiveStream { */
/* inner: inner as *mut hs::hs_stream, */
/* _ph: PhantomData, */
/* }; */

/* unsafe { &mut *p_matcher }.try_reset().await?; */
/* Ok(StreamSink { */
/* live, */
/* flags, */
/* scratch, */
/* matcher, */
/* }) */
/* } */
/* } */

/* pub enum CompressReserveBehavior { */
/* NewBuf, */
/* ExpandBuf(Vec<c_char>), */
/* FixedSizeBuf(Vec<c_char>), */
/* } */

/* pub(crate) enum ReserveResponse { */
/* MadeSpace(Vec<c_char>), */
/* NoSpace(Vec<c_char>), */
/* } */

/* impl CompressReserveBehavior { */
/* pub(crate) fn reserve(self, n: usize) -> ReserveResponse { */
/* match self { */
/* Self::NewBuf => ReserveResponse::MadeSpace(Vec::with_capacity(n)), */
/* Self::ExpandBuf(mut buf) => { */
/* if n > buf.capacity() { */
/* let additional = n - buf.capacity(); */
/* buf.reserve(additional); */
/* } */
/* ReserveResponse::MadeSpace(buf) */
/* }, */
/* Self::FixedSizeBuf(buf) => { */
/* if buf.capacity() <= n { */
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

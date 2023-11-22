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
use tokio::{sync::mpsc, task};

use std::{
  marker::PhantomData,
  mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
  sync::Arc,
};

pub trait Ops {
  type Err;
}

pub trait HandleOps: Ops {
  type OClone;
  async fn try_clone(&self) -> Result<Self::OClone, Self::Err>;
}

pub trait ResourceOps: Ops {
  type OOpen;
  type Params;
  async fn try_open(p: Self::Params) -> Result<Self::OOpen, Self::Err>;
  async fn try_drop(&mut self) -> Result<(), Self::Err>;
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct InputIndex(pub u32);

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
/// let results: Vec<(InputIndex, &str)> =
///   rx.map(|StreamMatch { input, range, .. }| (input, &msgs[range])).collect().await;
/// assert_eq!(results, vec![
///   (InputIndex(1), "aardvark"),
///   (InputIndex(2), "asdf"),
///   (InputIndex(2), "was"),
///   (InputIndex(2), "a"),
///   (InputIndex(2), "friend"),
///   (InputIndex(3), "after"),
///   (InputIndex(3), "all"),
/// ]);
/// # Ok(())
/// # })}
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StreamMatch {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub input: InputIndex,
  pub flags: ScanFlags,
}

pub trait StreamScanner {
  fn stream_scan(&mut self, m: &StreamMatch) -> MatchResult;
}

pub trait StreamOps: HandleOps {
  async fn try_reset(&mut self) -> Result<(), Self::Err>;
  async fn try_reset_and_copy(&self) -> Result<Self::OClone, Self::Err>;
}

pub struct StreamMatcher<S> {
  pub matches_tx: mpsc::Sender<StreamMatch>,
  pub handler: S,
  pub cur_idx: InputIndex,
}

impl<S: StreamScanner> StreamMatcher<S> {
  #[inline(always)]
  pub fn push_new_match(&mut self, m: StreamMatch) { self.matches_tx.blocking_send(m).unwrap(); }

  #[inline(always)]
  pub fn handle_match(&mut self, m: &StreamMatch) -> MatchResult { (self.handler).stream_scan(m) }

  #[inline(always)]
  pub fn get_next_input_index(&mut self) -> InputIndex {
    let ret = self.cur_idx;
    self.cur_idx.0 += 1;
    ret
  }
}

impl<S: Ops> Ops for StreamMatcher<S> {
  type Err = S::Err;
}

impl<S: HandleOps<OClone=S>> HandleOps for StreamMatcher<S> {
  type OClone = Self;

  async fn try_clone(&self) -> Result<Self, Self::Err> {
    Ok(Self {
      matches_tx: self.matches_tx.clone(),
      handler: self.handler.try_clone().await?,
      cur_idx: self.cur_idx,
    })
  }
}

impl<S: Clone> Clone for StreamMatcher<S> {
  fn clone(&self) -> Self {
    Self {
      matches_tx: self.matches_tx.clone(),
      handler: self.handler.clone(),
      cur_idx: self.cur_idx,
    }
  }
}

impl<S: StreamOps<OClone=S>> StreamOps for StreamMatcher<S> {
  async fn try_reset(&mut self) -> Result<(), Self::Err> {
    self.handler.try_reset().await?;
    self.cur_idx.0 = 0;
    Ok(())
  }

  async fn try_reset_and_copy(&self) -> Result<Self::OClone, Self::Err> {
    Ok(Self {
      matches_tx: self.matches_tx.clone(),
      handler: self.handler.try_reset_and_copy().await?,
      cur_idx: InputIndex(0),
    })
  }
}

pub struct CompressedStream<S> {
  pub buf: Vec<c_char>,
  pub flags: ScanFlags,
  pub scratch: Arc<Scratch>,
  pub matcher: Arc<StreamMatcher<S>>,
}

impl<S: Send+Sync> CompressedStream<S> {
  pub(crate) async fn compress<'db>(
    into: CompressReserveBehavior,
    live: &LiveStream<'db>,
    flags: ScanFlags,
    scratch: &Arc<Scratch>,
    matcher: &Arc<StreamMatcher<S>>,
  ) -> Result<Self, CompressionError> {
    let live: *const LiveStream<'db> = live;
    let live = live as usize;

    let buf = task::spawn_blocking(move || {
      let live: *const LiveStream<'db> = unsafe { &*(live as *const LiveStream<'db>) };

      let mut required_space = mem::MaybeUninit::<usize>::zeroed();
      assert_eq!(
        Err(HyperscanError::InsufficientSpace),
        HyperscanError::from_native(unsafe {
          hs::hs_compress_stream(
            (*live).as_ref_native(),
            ptr::null_mut(),
            0,
            required_space.as_mut_ptr(),
          )
        })
      );
      let mut required_space = unsafe { required_space.assume_init() };

      match into.reserve(required_space) {
        ReserveResponse::NoSpace(_) => Err(CompressionError::NoSpace(required_space)),
        ReserveResponse::MadeSpace(mut buf) => {
          HyperscanError::from_native(unsafe {
            hs::hs_compress_stream(
              (*live).as_ref_native(),
              buf.as_mut_ptr(),
              required_space,
              &mut required_space,
            )
          })?;
          Ok(buf)
        },
      }
    })
    .await
    .unwrap()?;

    Ok(Self {
      buf,
      flags,
      scratch: scratch.clone(),
      matcher: matcher.clone(),
    })
  }

  pub async fn expand(&self) -> Result<StreamSink<'db, S>, HyperscanError> {
    let s: *const Self = self;
    let s = s as usize;

    let (inner, flags) = task::spawn_blocking(move || {
      let Self {
        scratch,
        buf,
        flags,
        ..
      } = unsafe { &*(s as *const Self) };
      let mut inner = ptr::null_mut();
      HyperscanError::from_native(unsafe {
        hs::hs_expand_stream(
          scratch.db_ref_native().get_ref(),
          &mut inner,
          buf.as_ptr(),
          buf.capacity(),
        )
      })?;
      Ok::<_, HyperscanError>((inner as usize, *flags))
    })
    .await
    .unwrap()?;

    let live = LiveStream {
      inner: inner as *mut hs::hs_stream,
      _ph: PhantomData,
    };
    Ok(StreamSink {
      live,
      flags,
      scratch: self.scratch.clone(),
      matcher: self.matcher.clone(),
    })
  }
}

impl<'db> CompressedStream<'db, AcceptMatches> {
  pub async fn expand_and_reset(&self) -> Result<StreamSink<'db, AcceptMatches>, HyperscanError> {
    let s: *const Self = self;
    let s = s as usize;

    let mut scratch = self.scratch.clone();
    let p_scratch: *mut hs::hs_scratch = Arc::make_mut(&mut scratch).as_mut_native();
    let p_scratch = p_scratch as usize;

    let mut matcher = self.matcher.clone();
    let p_matcher: *mut StreamMatcher<AcceptMatches> = Arc::make_mut(&mut matcher);
    let p_matcher_n = p_matcher as usize;

    let (inner, flags) = task::spawn_blocking(move || {
      let Self { buf, flags, .. } = unsafe { &*(s as *const Self) };

      let mut stream = mem::MaybeUninit::<hs::hs_stream>::uninit();
      HyperscanError::from_native(unsafe {
        hs::hs_reset_and_expand_stream(
          stream.as_mut_ptr(),
          buf.as_ptr(),
          buf.capacity(),
          p_scratch as *mut hs::hs_scratch,
          Some(match_slice_stream),
          p_matcher_n as *mut c_void,
        )
      })?;
      Ok::<_, HyperscanError>((stream.as_mut_ptr() as usize, *flags))
    })
    .await
    .unwrap()?;

    let live = LiveStream {
      inner: inner as *mut hs::hs_stream,
      _ph: PhantomData,
    };

    unsafe { &mut *p_matcher }.try_reset().await?;
    Ok(StreamSink {
      live,
      flags,
      scratch,
      matcher,
    })
  }
}

pub enum CompressReserveBehavior {
  NewBuf,
  ExpandBuf(Vec<c_char>),
  FixedSizeBuf(Vec<c_char>),
}

pub(crate) enum ReserveResponse {
  MadeSpace(Vec<c_char>),
  NoSpace(Vec<c_char>),
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

#[derive(Debug, Display, Error)]
pub enum CompressionError {
  /// other error: {0}
  Other(#[from] HyperscanError),
  /// not enough space for {0} in buf
  NoSpace(usize),
}

pub struct LiveStream<'db> {
  inner: *mut hs::hs_stream,
  _ph: PhantomData<&'db u8>,
}

unsafe impl<'db> Send for LiveStream<'db> {}
unsafe impl<'db> Sync for LiveStream<'db> {}

impl<'db> LiveStream<'db> {
  #[inline]
  pub(crate) const fn as_ref_native(&self) -> &hs::hs_stream { unsafe { &*self.inner } }

  #[inline]
  pub(crate) const fn as_mut_native(&mut self) -> &mut hs::hs_stream { unsafe { &mut *self.inner } }
}

impl<'db> Ops for LiveStream<'db> {
  type Err = HyperscanError;
}

impl<'db> HandleOps for LiveStream<'db> {
  type OClone = Self;

  async fn try_clone(&self) -> Result<Self, HyperscanError> {
    let mut stream_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe {
      hs::hs_copy_stream(&mut stream_ptr, self.as_ref_native())
    })?;
    Ok(Self {
      inner: stream_ptr,
      _ph: PhantomData,
    })
  }
}

impl<'db> ResourceOps for LiveStream<'db> {
  type OOpen = Self;
  type Params = (ScanFlags, &'db Database);

  async fn try_open(p: (ScanFlags, &'db Database)) -> Result<Self, HyperscanError> {
    let (flags, db) = p;
    let mut stream_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe {
      hs::hs_open_stream(db.as_ref_native(), flags.into_native(), &mut stream_ptr)
    })?;
    Ok(Self {
      inner: stream_ptr,
      _ph: PhantomData,
    })
  }

  async fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_close_stream(self.as_mut_native(), ptr::null_mut(), None, ptr::null_mut())
    })
  }
}

impl<'db> StreamOps for LiveStream<'db> {
  async fn try_reset(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_reset_stream(
        self.as_mut_native(),
        ScanFlags::default().into_native(),
        ptr::null_mut(),
        None,
        ptr::null_mut(),
      )
    })
  }

  async fn try_reset_and_copy(&self) -> Result<Self, HyperscanError> {
    let mut to = mem::MaybeUninit::<hs::hs_stream>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_reset_and_copy_stream(
        to.as_mut_ptr(),
        self.as_ref_native(),
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

pub struct StreamSink<'db, S> {
  live: LiveStream<'db>,
  flags: ScanFlags,
  scratch: Arc<Scratch>,
  matcher: Arc<StreamMatcher<S>>,
}

impl<'db, S: Ops> Ops for StreamSink<'db, S> {
  type Err = S::Err;
}

impl<'db> ResourceOps for StreamSink<'db, AcceptMatches> {
  type OOpen = Self;
  type Params = (ScanFlags, &'db Database, mpsc::Sender<StreamMatch>);

  async fn try_open(
    p: (ScanFlags, &'db Database, mpsc::Sender<StreamMatch>),
  ) -> Result<Self, Self::Err> {
    let (flags, db, tx) = p;
    let live = LiveStream::try_open((flags, db)).await?;
    let scratch = Arc::new(Scratch::try_open(Pin::new(db)).await?);
    let matcher = Arc::new(StreamMatcher {
      matches_tx: tx,
      handler: AcceptMatches::try_open(()).await?,
      cur_idx: InputIndex(0),
    });
    Ok(Self {
      live,
      flags,
      scratch,
      matcher,
    })
  }

  async fn try_drop(&mut self) -> Result<(), Self::Err> {
    let s: *mut Self = self;
    let s = s as usize;

    task::spawn_blocking(move || {
      let Self {
        live,
        scratch,
        matcher,
        ..
      } = unsafe { &mut *(s as *mut Self) };
      let matcher: *mut StreamMatcher<AcceptMatches> = Arc::make_mut(matcher);
      let matcher = matcher as usize;

      HyperscanError::from_native(unsafe {
        hs::hs_close_stream(
          live.as_mut_native(),
          Arc::make_mut(scratch).as_mut_native(),
          Some(match_slice_stream),
          matcher as *mut c_void,
        )
      })
    })
    .await
    .unwrap()?;

    Ok(())
  }
}

impl<'db, S: HandleOps<OClone=S, Err=HyperscanError>> HandleOps for StreamSink<'db, S> {
  type OClone = Self;

  async fn try_clone(&self) -> Result<Self, S::Err> {
    Ok(Self {
      live: self.live.try_clone().await?,
      flags: self.flags,
      scratch: self.scratch.clone(),
      matcher: self.matcher.clone(),
    })
  }
}

impl<'db> StreamOps for StreamSink<'db, AcceptMatches> {
  async fn try_reset(&mut self) -> Result<(), Self::Err> {
    let s: *mut Self = self;
    let s = s as usize;

    task::spawn_blocking(move || {
      let Self {
        live,
        scratch,
        matcher,
        flags,
      } = unsafe { &mut *(s as *mut Self) };
      let matcher: *mut StreamMatcher<AcceptMatches> = Arc::make_mut(matcher);
      let matcher = matcher as usize;

      HyperscanError::from_native(unsafe {
        hs::hs_reset_stream(
          live.as_mut_native(),
          flags.into_native(),
          Arc::make_mut(scratch).as_mut_native(),
          Some(match_slice_stream),
          matcher as *mut c_void,
        )
      })
    })
    .await
    .unwrap()?;

    Arc::make_mut(&mut self.matcher).try_reset().await?;
    Ok(())
  }

  async fn try_reset_and_copy(&self) -> Result<Self, Self::Err> {
    let s: *const Self = self;
    let s = s as usize;

    let (to, flags) = task::spawn_blocking(move || {
      let Self {
        live,
        flags,
        scratch,
        matcher,
      } = unsafe { &mut *(s as *mut Self) };
      let matcher: *mut StreamMatcher<AcceptMatches> = Arc::make_mut(matcher);
      let matcher = matcher as usize;

      let mut to = mem::MaybeUninit::<hs::hs_stream>::uninit();
      HyperscanError::from_native(unsafe {
        hs::hs_reset_and_copy_stream(
          to.as_mut_ptr(),
          live.as_ref_native(),
          Arc::make_mut(scratch).as_mut_native(),
          Some(match_slice_stream),
          matcher as *mut c_void,
        )
      })?;
      Ok::<_, Self::Err>((to.as_mut_ptr() as usize, *flags))
    })
    .await
    .unwrap()?;
    let live = LiveStream {
      inner: to as *mut hs::hs_stream,
      _ph: PhantomData,
    };

    let matcher = Arc::new(self.matcher.try_reset_and_copy().await?);

    Ok(Self {
      live,
      flags,
      scratch: self.scratch.clone(),
      matcher,
    })
  }
}

#[derive(Clone)]
pub struct AcceptMatches;

impl StreamScanner for AcceptMatches {
  fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult { MatchResult::Continue }
}

impl Ops for AcceptMatches {
  type Err = HyperscanError;
}

impl HandleOps for AcceptMatches {
  type OClone = Self;

  async fn try_clone(&self) -> Result<Self, Self::Err> { Ok(self.clone()) }
}

impl ResourceOps for AcceptMatches {
  type OOpen = Self;
  type Params = ();

  async fn try_open(_p: ()) -> Result<Self, Self::Err> { Ok(Self) }

  async fn try_drop(&mut self) -> Result<(), Self::Err> { Ok(()) }
}

impl StreamOps for AcceptMatches {
  async fn try_reset(&mut self) -> Result<(), Self::Err> { Ok(()) }

  async fn try_reset_and_copy(&self) -> Result<Self, Self::Err> { Ok(self.clone()) }
}

impl<'db> StreamSink<'db, AcceptMatches> {
  pub async fn scan(
    &mut self,
    data: ByteSlice<'_>,
    flags: ScanFlags,
  ) -> Result<(), HyperscanError> {
    let data_len = data.native_len();
    let data = data.as_ptr() as usize;
    self.flags = flags;
    let s: *mut Self = self;
    let s = s as usize;

    task::spawn_blocking(move || {
      let Self {
        live,
        scratch,
        matcher,
        flags,
      } = unsafe { &mut *(s as *mut Self) };
      let matcher = Arc::make_mut(matcher);
      let _ = matcher.get_next_input_index();
      let p_matcher: *mut StreamMatcher<AcceptMatches> = matcher;
      let p_matcher = p_matcher as usize;
      HyperscanError::from_native(unsafe {
        hs::hs_scan_stream(
          live.as_mut_native(),
          data as *const c_char,
          data_len,
          flags.into_native(),
          Arc::make_mut(scratch).as_mut_native(),
          Some(match_slice_stream),
          p_matcher as *mut c_void,
        )
      })?;
      Ok(())
    })
    .await
    .unwrap()
  }
}

impl<'db, S: Send+Sync> StreamSink<'db, S> {
  ///```
  /// # fn main() -> Result<(), eyre::Report> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, state::*, stream::*};
  /// use futures_util::StreamExt;
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(
  ///   Flags::UTF8 | Flags::SOM_LEFTMOST,
  ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE,
  /// )?;
  ///
  /// let flags = ScanFlags::default();
  /// let Streamer { mut sink, mut rx } = Streamer::try_open((flags, &db, 32)).await?;
  ///
  /// let buf = sink.compress(CompressReserveBehavior::NewBuf).await?;
  /// sink.try_drop().await?;
  /// std::mem::drop(sink);
  ///
  /// let msg = "aardvark";
  /// let mut sink = buf.expand().await?;
  /// sink.scan(msg.as_bytes().into(), flags).await?;
  /// sink.try_drop().await?;
  /// std::mem::drop(sink);
  ///
  /// // Although there are further senders in Arc shared pointers,
  /// // we cut them off here in order to ensure our stream terminates.
  /// rx.close();
  /// let rx = tokio_stream::wrappers::ReceiverStream::new(rx);
  /// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }| &msg[range]).collect().await;
  /// assert_eq!(results, vec!["a", "aa", "a"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub async fn compress(
    &self,
    into: CompressReserveBehavior,
  ) -> Result<CompressedStream<'db, S>, CompressionError> {
    let Self {
      live,
      flags,
      scratch,
      matcher,
    } = self;
    CompressedStream::compress(into, live, *flags, scratch, matcher).await
  }
}

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
pub struct Streamer<'db, S> {
  pub sink: StreamSink<'db, S>,
  pub rx: mpsc::Receiver<StreamMatch>,
}

impl<'db, S: Ops<Err=HyperscanError>> Ops for Streamer<'db, S> {
  type Err = HyperscanError;
}

impl<'db> ResourceOps for Streamer<'db, AcceptMatches> {
  type OOpen = Self;
  type Params = (ScanFlags, &'db Database, usize);

  async fn try_open(p: (ScanFlags, &'db Database, usize)) -> Result<Self, HyperscanError> {
    let (flags, db, n) = p;
    let (tx, rx) = mpsc::channel(n);
    let sink = StreamSink::try_open((flags, db, tx)).await?;
    Ok(Self { sink, rx })
  }

  async fn try_drop(&mut self) -> Result<(), HyperscanError> {
    self.sink.try_drop().await?;
    Ok(())
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
    flags,
    context,
  } = MatchEvent::coerce_args(id, from, to, flags, context);
  let mut matcher: Pin<&mut StreamMatcher<AcceptMatches>> =
    MatchEvent::extract_context::<'_, StreamMatcher<AcceptMatches>>(context).unwrap();
  let m = StreamMatch {
    input: matcher.cur_idx,
    id,
    range,
    flags,
  };

  let result = matcher.handle_match(&m);
  if result == MatchResult::Continue {
    matcher.push_new_match(m);
  }

  result.into_native()
}

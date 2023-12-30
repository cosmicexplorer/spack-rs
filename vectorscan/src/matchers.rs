/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Types used in vectorscan match callbacks.

use cfg_if::cfg_if;
use displaydoc::Display;

#[cfg(feature = "catch-unwind")]
use std::{
  any::Any,
  panic::{self, AssertUnwindSafe, RefUnwindSafe, UnwindSafe},
};
use std::{
  fmt, mem, ops,
  os::raw::{c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
};

/// Reference to the source expression that produced a match result or error.
///
/// This is provided to match results such as [`Match`] as well as errors like
/// [`CompileError`](crate::error::CompileError).
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(
  /// This corresponds to the value of an
  /// [`ExprId`](crate::expression::ExprId) argument provided during expression
  /// set compilation, but will be `0` if only a single expression
  /// was compiled or if no expression ids were provided.
  pub c_uint,
);

impl fmt::Display for ExpressionIndex {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<{}>", self.0) }
}

impl From<c_uint> for ExpressionIndex {
  fn from(x: c_uint) -> Self { Self(x) }
}

/// Return value for all match callbacks.
#[derive(
  Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, num_enum::IntoPrimitive,
)]
#[repr(u8)]
#[ignore_extra_doc_attributes]
pub enum MatchResult {
  /// Continue matching.
  Continue = 0,
  /// Immediately cease matching.
  ///
  /// In scanning is performed in block or vectored mode and this value is
  /// returned, the scan will simply terminate immediately. If scanning is
  /// performed in streaming mode and this value is returned, any subsequent
  /// calls to
  /// [`Scratch::scan_sync_stream()`](crate::state::Scratch::scan_sync_stream)
  /// or [`ScratchStreamSink::scan()`](crate::stream::ScratchStreamSink::scan)
  /// for the same stream will also immediately return with
  /// [`ScanTerminated`](crate::error::VectorscanRuntimeError::ScanTerminated).
  /* This is documented to be just any non-zero value at the moment. */
  CeaseMatching = 1,
}

impl MatchResult {
  /* TODO: num_enum for const IntoPrimitive! */
  pub(crate) fn into_native(self) -> c_int {
    let x: u8 = self.into();
    x.into()
  }
}

#[derive(Debug)]
pub(crate) struct MatchEvent {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub context: Option<ptr::NonNull<c_void>>,
}

impl MatchEvent {
  pub fn coerce_args(id: c_uint, from: c_ulonglong, to: c_ulonglong, context: *mut c_void) -> Self {
    static_assertions::assert_eq_size!(c_uint, ExpressionIndex);
    static_assertions::const_assert!(mem::size_of::<usize>() >= mem::size_of::<c_ulonglong>());
    static_assertions::assert_eq_size!(ops::Range<usize>, (c_ulonglong, c_ulonglong));
    debug_assert!(from <= to);
    Self {
      id: ExpressionIndex(id),
      range: ops::Range {
        start: from as usize,
        end: to as usize,
      },
      context: ptr::NonNull::new(context),
    }
  }

  pub unsafe fn extract_context<'a, T>(context: ptr::NonNull<c_void>) -> Pin<&'a mut T> {
    Pin::new_unchecked(&mut *mem::transmute::<*mut c_void, *mut T>(
      context.as_ptr(),
    ))
  }
}

pub(crate) mod contiguous_slice {
  use super::*;
  use crate::sources::ByteSlice;

  /// Match object returned when searching a single contiguous string.
  ///
  /// This is returned by e.g.
  /// [`Scratch::scan_sync()`](crate::state::Scratch::scan_sync).
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Match<'a> {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The entire text matching the given pattern.
    pub source: ByteSlice<'a>,
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub(crate) struct SliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        handler: &'code mut (dyn FnMut(Match<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      pub(crate) struct SliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        handler: &'code mut (dyn FnMut(Match<'data>) -> MatchResult),
      }
    }
  }

  impl<'data, 'code> SliceMatcher<'data, 'code> {
    pub fn new<F: FnMut(Match<'data>) -> MatchResult>(
      parent_slice: ByteSlice<'data>,
      f: &'code mut F,
    ) -> Self {
      let f: &'code mut (dyn FnMut(Match<'data>) -> MatchResult) = f;
      #[cfg(feature = "catch-unwind")]
      let f: &'code mut (dyn FnMut(Match<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(f) };
      Self {
        parent_slice,
        handler: f,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: Match<'data>,
    ) -> Result<MatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: Match<'data>) -> MatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          MatchResult::CeaseMatching
        },
      }
    }

    pub fn handle_match(&mut self, m: Match<'data>) -> MatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.handler)(m)
        }
      }
    }

    pub fn resume_panic(self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  pub(crate) extern "C" fn match_slice(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, context);
    let mut slice_matcher: Pin<&mut SliceMatcher> =
      unsafe { MatchEvent::extract_context(context.unwrap()) };

    if slice_matcher.has_panic() {
      return MatchResult::CeaseMatching.into_native();
    }

    let matched_substring = slice_matcher.index_range(range);
    let m = Match {
      id,
      source: matched_substring,
    };

    let result = slice_matcher.handle_match(m);
    result.into_native()
  }
}
pub use contiguous_slice::Match;

#[cfg(feature = "vectored")]
pub(crate) mod vectored_slice {
  use super::*;
  use crate::sources::vectored::{VectoredByteSlices, VectoredSubset};

  /// Match object returned when searching vectored string data.
  ///
  /// This is returned by e.g.
  /// [`Scratch::scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored).
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct VectoredMatch<'a> {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The entire "ragged" subset of vectored string data matching the given
    /// pattern.
    pub source: VectoredSubset<'a, 'a>,
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub(crate) struct VectoredMatcher<'data, 'code> {
        parent_slices: VectoredByteSlices<'data, 'data>,
        handler: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      pub(crate) struct VectoredMatcher<'data, 'code> {
        parent_slices: VectoredByteSlices<'data, 'data>,
        handler: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult),
      }
    }
  }

  impl<'data, 'code> VectoredMatcher<'data, 'code> {
    pub fn new<F: FnMut(VectoredMatch<'data>) -> MatchResult>(
      parent_slices: VectoredByteSlices<'data, 'data>,
      f: &'code mut F,
    ) -> Self {
      let f: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult) = f;
      #[cfg(feature = "catch-unwind")]
      let f: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(f) };
      Self {
        parent_slices,
        handler: f,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn parent_slices(&self) -> VectoredByteSlices<'data, 'data> { self.parent_slices }

    pub fn index_range(&self, range: ops::Range<usize>) -> VectoredSubset<'data, 'data> {
      self.parent_slices.index_range(range).unwrap()
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: VectoredMatch<'data>,
    ) -> Result<MatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: VectoredMatch<'data>) -> MatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          MatchResult::CeaseMatching
        },
      }
    }

    pub fn handle_match(&mut self, m: VectoredMatch<'data>) -> MatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.handler)(m)
        }
      }
    }

    pub fn resume_panic(self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  pub(crate) extern "C" fn match_slice_vectored(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, context);
    let mut slice_matcher: Pin<&mut VectoredMatcher> =
      unsafe { MatchEvent::extract_context(context.unwrap()) };

    if slice_matcher.has_panic() {
      return MatchResult::CeaseMatching.into_native();
    }

    let matched_substring = slice_matcher.index_range(range);
    let m = VectoredMatch {
      id,
      source: matched_substring,
    };

    let result = slice_matcher.handle_match(m);
    result.into_native()
  }
}
#[cfg(feature = "vectored")]
#[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
pub use vectored_slice::VectoredMatch;

#[cfg(feature = "stream")]
#[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
pub mod stream {
  use super::*;
  use crate::sources::stream::Range;

  // ///```
  // /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
  // tokio_test::block_on(async { /// use vectorscan::{expression::*,
  // matchers::*, flags::*, stream::*}; /// use futures_util::StreamExt;
  // ///
  // /// let expr: Expression = r"\b\w+\b".parse()?;
  // /// let db = expr.compile(
  // ///   Flags::UTF8 | Flags::SOM_LEFTMOST,
  // ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE,
  // /// )?;
  // /// let scratch = db.allocate_scratch()?;
  // ///
  // /// struct S;
  // /// impl StreamScanner for S {
  // ///   fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult {
  // MatchResult::Continue } ///   fn new() -> Self where Self: Sized { Self }
  // ///   fn reset(&mut self) {}
  // ///   fn boxed_clone(&self) -> Box<dyn StreamScanner> { Box::new(Self) }
  // /// }
  // ///
  // /// let mut s = Streamer::open::<S>(&db, scratch.into())?;
  // ///
  // /// let msg1 = "aardvark ";
  // /// s.scan(msg1.as_bytes().into()).await?;
  // ///
  // /// let msg2 = "asdf was a friend ";
  // /// s.scan(msg2.as_bytes().into()).await?;
  // ///
  // /// let msg3 = "after all";
  // /// s.scan(msg3.as_bytes().into()).await?;
  // /// s.flush_eod().await?;
  // /// let rx = s.stream_results();
  // ///
  // /// let msgs: String = [msg1, msg2, msg3].concat();
  // /// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }|
  // &msgs[range]).collect().await; /// assert_eq!(results, vec![
  // ///   "aardvark",
  // ///   "asdf",
  // ///   "was",
  // ///   "a",
  // ///   "friend",
  // ///   "after",
  // ///   "all",
  // /// ]);
  // /// # Ok(())
  // /// # })}
  // /// ```
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct StreamMatch {
    pub id: ExpressionIndex,
    pub range: Range,
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub struct StreamMatcher<'code> {
        handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+UnwindSafe+RefUnwindSafe+'code),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      #[repr(transparent)]
      pub struct StreamMatcher<'code> {
        handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+'code),
      }
    }
  }

  impl<'code> StreamMatcher<'code> {
    pub fn new(handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+'code)) -> Self {
      #[cfg(feature = "catch-unwind")]
      let handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+UnwindSafe+RefUnwindSafe+'code) =
        unsafe { mem::transmute(handler) };
      Self {
        handler,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: StreamMatch,
    ) -> Result<MatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: StreamMatch) -> MatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          MatchResult::CeaseMatching
        },
      }
    }

    pub fn handle_match(&mut self, m: StreamMatch) -> MatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.handler)(m)
        }
      }
    }

    pub fn resume_panic(&mut self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload.take() {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  #[repr(transparent)]
  pub(crate) struct SendStreamMatcher<'code>(StreamMatcher<'code>);

  impl<'code> SendStreamMatcher<'code> {
    pub fn new(handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code)) -> Self {
      Self(StreamMatcher::new(handler))
    }

    pub fn as_mut_basic(&mut self) -> &mut StreamMatcher<'code> { unsafe { mem::transmute(self) } }
  }

  static_assertions::assert_eq_size!(
    &'static mut (dyn FnMut(StreamMatch) -> MatchResult+Send),
    &'static mut (dyn FnMut(StreamMatch) -> MatchResult)
  );
  static_assertions::assert_eq_size!(StreamMatcher<'static>, SendStreamMatcher<'static>);

  unsafe impl<'code> Send for SendStreamMatcher<'code> {}

  pub(crate) extern "C" fn match_slice_stream(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, context);
    let mut matcher: Pin<&mut StreamMatcher> =
      unsafe { MatchEvent::extract_context(context.unwrap()) };

    if matcher.has_panic() {
      return MatchResult::CeaseMatching.into_native();
    }

    let m = StreamMatch {
      id,
      range: range.into(),
    };

    let result = matcher.handle_match(m);
    result.into_native()
  }
}

/// Types used in chimera match callbacks.
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;
  use crate::{error::chimera::*, hs, sources::ByteSlice};

  use smallvec::SmallVec;

  use std::{hash, slice};

  /// Return value for all chimera match callbacks.
  #[derive(
    Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, num_enum::IntoPrimitive,
  )]
  #[repr(u8)]
  pub enum ChimeraMatchResult {
    /// Continue matching.
    Continue = hs::CH_CALLBACK_CONTINUE,
    /// Terminate matching.
    Terminate = hs::CH_CALLBACK_TERMINATE,
    /// Skip remaining matches for this ID and continue.
    SkipPattern = hs::CH_CALLBACK_SKIP_PATTERN,
  }

  impl ChimeraMatchResult {
    /* TODO: num_enum for const IntoPrimitive! */
    pub(crate) fn into_native(self) -> hs::ch_callback_t {
      let x: u8 = self.into();
      x.into()
    }
  }

  #[derive(Debug)]
  struct ChimeraMatchEvent<'a> {
    pub id: ExpressionIndex,
    pub range: ops::Range<usize>,
    pub captures: Option<&'a [hs::ch_capture]>,
    pub context: Option<ptr::NonNull<c_void>>,
  }

  impl<'a> ChimeraMatchEvent<'a> {
    pub fn coerce_args(
      id: c_uint,
      from: c_ulonglong,
      to: c_ulonglong,
      size: c_uint,
      captured: *const hs::ch_capture,
      context: *mut c_void,
    ) -> Self {
      debug_assert!(from <= to);
      Self {
        id: ExpressionIndex(id),
        range: ops::Range {
          start: from as usize,
          end: to as usize,
        },
        captures: if captured.is_null() || size == 0 {
          None
        } else {
          Some(unsafe { slice::from_raw_parts(captured, size as usize) })
        },
        context: ptr::NonNull::new(context),
      }
    }

    pub unsafe fn extract_context<'c, T>(context: ptr::NonNull<c_void>) -> Pin<&'c mut T> {
      MatchEvent::extract_context(context)
    }
  }

  /// Match object returned when searching a single contiguous string.
  ///
  /// This is returned by e.g.
  /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync).
  /// Note that unlike e.g. [`super::Match`], this does not implement [`Copy`],
  /// as it may need to keep track of owned heap data in [`Self::captures`].
  /// However, if
  /// [`ChimeraMode::NOGROUPS`](crate::flags::chimera::ChimeraMode::NOGROUPS) is
  /// used, [`Self::captures`] will always be [`None`], and `.clone()` can be
  /// called without any heap allocation. As an additional optimization,
  /// patterns with up to 9 capturing groups (the 0th group being the entire
  /// match) are stored on the stack.
  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
  pub struct ChimeraMatch<'a> {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The entire text matching the given pattern.
    pub source: ByteSlice<'a>,
    /// Captured text, if
    /// [`ChimeraMode::GROUPS`](crate::flags::chimera::ChimeraMode::GROUPS) was
    /// specified during compilation.
    ///
    /// Individual captures are themselves optional because of patterns like
    /// `"hell(o)?"`, which would produce [`None`] for the 1st capture if
    /// the pattern `o` isn't matched. The 0th capture always corresponds to
    /// the entire match text, so it is always [`Some`] and should always be
    /// equal to [`Self::source`].
    pub captures: Option<SmallVec<Option<ByteSlice<'a>>, 10>>,
  }

  impl<'a> hash::Hash for ChimeraMatch<'a> {
    fn hash<H>(&self, state: &mut H)
    where H: hash::Hasher {
      self.id.hash(state);
      self.source.hash(state);
      if let Some(ref captures) = self.captures {
        captures[..].hash(state);
      }
    }
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub(crate) struct ChimeraSliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        match_handler: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe),
        error_handler: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      pub(crate) struct ChimeraSliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        match_handler: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult),
        error_handler: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult),
      }
    }
  }

  impl<'data, 'code> ChimeraSliceMatcher<'data, 'code> {
    pub fn new(
      parent_slice: ByteSlice<'data>,
      matcher: &'code mut impl FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult,
      error: &'code mut impl FnMut(ChimeraMatchError) -> ChimeraMatchResult,
    ) -> Self {
      let matcher: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult) = matcher;
      #[cfg(feature = "catch-unwind")]
      let matcher: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(matcher) };
      let error: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult) = error;
      #[cfg(feature = "catch-unwind")]
      let error: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(error) };
      Self {
        parent_slice,
        match_handler: matcher,
        error_handler: error,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: ChimeraMatch<'data>,
    ) -> Result<ChimeraMatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.match_handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: ChimeraMatch<'data>) -> ChimeraMatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          ChimeraMatchResult::Terminate
        },
      }
    }

    pub fn handle_match(&mut self, m: ChimeraMatch<'data>) -> ChimeraMatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.match_handler)(m)
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_error_with_panic(
      &mut self,
      e: ChimeraMatchError,
    ) -> Result<ChimeraMatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.error_handler);
      panic::catch_unwind(move || f(e))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_error_wrapping_panic(&mut self, e: ChimeraMatchError) -> ChimeraMatchResult {
      match self.handle_error_with_panic(e) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          ChimeraMatchResult::Terminate
        },
      }
    }

    pub fn handle_error(&mut self, e: ChimeraMatchError) -> ChimeraMatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_error_wrapping_panic(e)
        } else {
          (self.error_handler)(e)
        }
      }
    }

    pub fn resume_panic(self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  pub(crate) extern "C" fn match_chimera_slice(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    size: c_uint,
    captured: *const hs::ch_capture,
    context: *mut c_void,
  ) -> hs::ch_callback_t {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let ChimeraMatchEvent {
      id,
      range,
      captures,
      context,
    } = ChimeraMatchEvent::coerce_args(id, from, to, size, captured, context);
    let mut matcher: Pin<&mut ChimeraSliceMatcher> =
      unsafe { ChimeraMatchEvent::extract_context(context.unwrap()) };

    if matcher.has_panic() {
      return ChimeraMatchResult::Terminate.into_native();
    }

    let matched_substring = matcher.index_range(range);
    let m = ChimeraMatch {
      id,
      source: matched_substring,
      captures: captures.map(|c| {
        c.iter()
          .map(|hs::ch_capture { flags, from, to }| {
            if *flags == hs::CH_CAPTURE_FLAG_INACTIVE as c_uint {
              None
            } else {
              debug_assert_eq!(*flags, hs::CH_CAPTURE_FLAG_ACTIVE as c_uint);
              debug_assert!(from <= to);
              let range = ops::Range {
                start: *from as usize,
                end: *to as usize,
              };
              Some(matcher.index_range(range))
            }
          })
          .collect()
      }),
    };

    let result = matcher.handle_match(m);
    result.into_native()
  }

  pub(crate) extern "C" fn error_callback_chimera(
    error_type: hs::ch_error_event_t,
    id: c_uint,
    info: *mut c_void,
    ctx: *mut c_void,
  ) -> hs::ch_callback_t {
    let error_type = ChimeraMatchErrorType::from_native(error_type);
    let id = ExpressionIndex(id);
    debug_assert!(info.is_null(), "info pointer is currently unused");
    let ctx = ptr::NonNull::new(ctx);
    let mut matcher: Pin<&mut ChimeraSliceMatcher> =
      unsafe { ChimeraMatchEvent::extract_context(ctx.unwrap()) };

    if matcher.has_panic() {
      return ChimeraMatchResult::Terminate.into_native();
    }

    let e = ChimeraMatchError { error_type, id };

    let result = matcher.handle_error(e);
    result.into_native()
  }
}
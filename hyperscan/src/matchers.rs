/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use displaydoc::Display;

use std::{
  cmp, fmt, mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr, slice, str,
};

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct ByteSlice<'a>(&'a [u8]);

impl<'a> ByteSlice<'a> {
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.0.get(range).map(Self)
  }

  pub const fn from_str(data: &'a str) -> Self { Self(data.as_bytes()) }

  pub const fn from_slice(data: &'a [u8]) -> Self { Self(data) }

  pub const fn as_slice(&self) -> &'a [u8] { unsafe { mem::transmute(self.0) } }

  pub const unsafe fn as_str(&self) -> &'a str { str::from_utf8_unchecked(self.as_slice()) }

  pub(crate) const fn as_ptr(&self) -> *const c_char { unsafe { mem::transmute(self.0.as_ptr()) } }

  pub const fn len(&self) -> usize { self.0.len() }

  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  pub(crate) const fn native_len(&self) -> c_uint { self.len() as c_uint }
}

impl<'a> From<&'a [u8]> for ByteSlice<'a> {
  fn from(x: &'a [u8]) -> Self { Self::from_slice(x) }
}

impl<'a, const N: usize> From<&'a [u8; N]> for ByteSlice<'a> {
  fn from(x: &'a [u8; N]) -> Self { Self::from_slice(x.as_ref()) }
}

impl<'a> From<&'a str> for ByteSlice<'a> {
  fn from(x: &'a str) -> Self { Self::from_str(x) }
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct VectoredByteSlices<'a>(&'a [ByteSlice<'a>]);

impl<'a> VectoredByteSlices<'a> {
  pub const fn from_slices(data: &'a [ByteSlice<'a>]) -> Self { Self(data) }

  pub(crate) fn pointers_and_lengths(&self) -> (Vec<*const c_char>, Vec<c_uint>) {
    let lengths: Vec<c_uint> = self.0.iter().map(|col| col.native_len()).collect();
    let data_pointers: Vec<*const c_char> = self.0.iter().map(|col| col.as_ptr()).collect();
    (data_pointers, lengths)
  }

  pub const fn len(&self) -> usize { self.0.len() }

  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  pub(crate) const fn native_len(&self) -> c_uint { self.len() as c_uint }

  fn find_index_at(
    &self,
    mut column: usize,
    mut within_column_index: usize,
    mut remaining: usize,
  ) -> Option<(usize, usize)> {
    let num_columns = self.0.len();
    if column >= num_columns {
      return None;
    }
    if remaining == 0 {
      return Some((column, within_column_index));
    }

    let within_column_index = loop {
      let cur_col = &self.0[column];
      let (prev, max_diff) = if within_column_index > 0 {
        let x = within_column_index;
        within_column_index = 0;
        assert_ne!(cur_col.0.len(), x);
        (x, cur_col.0.len() - x)
      } else {
        (0, cur_col.0.len())
      };
      assert_ne!(max_diff, 0);
      let new_offset = cmp::min(remaining, max_diff);
      let cur_ind = prev + new_offset;
      remaining -= new_offset;
      if remaining == 0 {
        break cur_ind;
      } else if column == (num_columns - 1) {
        return None;
      } else {
        column += 1;
      }
    };

    Some((column, within_column_index))
  }

  fn collect_slices_range(
    &self,
    start: (usize, usize),
    end: (usize, usize),
  ) -> Option<Vec<ByteSlice<'a>>> {
    let (start_col, start_ind) = start;
    let (end_col, end_ind) = end;
    assert!(end_col >= start_col);

    if start_col == end_col {
      assert!(end_ind >= start_ind);
      Some(vec![self.0[start_col].index_range(start_ind..end_ind)?])
    } else {
      let mut ret: Vec<ByteSlice<'a>> = Vec::with_capacity(end_col - start_col + 1);

      ret.push(self.0[start_col].index_range(start_ind..)?);
      for cur_col in (start_col + 1)..end_col {
        ret.push(self.0[cur_col]);
      }
      ret.push(self.0[end_col].index_range(..end_ind)?);
      Some(ret)
    }
  }

  pub fn index_range(&self, range: ops::Range<usize>) -> Option<Vec<ByteSlice<'a>>> {
    let ops::Range { start, end } = range;
    let (start_col, start_ind) = self.find_index_at(0, 0, start)?;
    let (end_col, end_ind) = self.find_index_at(start_col, start_ind, end - start)?;
    self.collect_slices_range((start_col, start_ind), (end_col, end_ind))
  }
}

impl<'a> From<&'a [ByteSlice<'a>]> for VectoredByteSlices<'a> {
  fn from(x: &'a [ByteSlice<'a>]) -> Self { Self::from_slices(x) }
}

impl<'a, const N: usize> From<&'a [ByteSlice<'a>; N]> for VectoredByteSlices<'a> {
  fn from(x: &'a [ByteSlice<'a>; N]) -> Self { Self::from_slices(x.as_ref()) }
}

impl<'a> From<&'a [&'a [u8]]> for VectoredByteSlices<'a> {
  fn from(x: &'a [&'a [u8]]) -> Self {
    let x: &'a [ByteSlice<'a>] = unsafe { mem::transmute(x) };
    Self(x)
  }
}

impl<'a, const N: usize> From<&'a [&'a [u8]; N]> for VectoredByteSlices<'a> {
  fn from(x: &'a [&'a [u8]; N]) -> Self {
    let x: &'a [ByteSlice<'a>; N] = unsafe { mem::transmute(x) };
    x.into()
  }
}

/// Reference to the source expression that produced a match result.
///
/// This corresponds to the value of an
/// [`ExprId`](crate::expression::ExprId) argument provided during expression
/// set compilation, but will be `0` if only a single expression
/// is compiled or no expression ids are provided.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub c_uint);

impl fmt::Display for ExpressionIndex {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<{}>", self.0) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
struct RangeIndex(pub c_ulonglong);

impl RangeIndex {
  pub const fn into_rust_index(self) -> usize {
    static_assertions::const_assert!(mem::size_of::<usize>() >= mem::size_of::<c_ulonglong>());
    self.0 as usize
  }

  pub const fn bounded_range(from: Self, to: Self) -> ops::Range<usize> {
    static_assertions::assert_eq_size!(ops::Range<usize>, (c_ulonglong, c_ulonglong));
    let from = from.into_rust_index();
    let to = to.into_rust_index();
    debug_assert!(from <= to);
    ops::Range {
      start: from,
      end: to,
    }
  }
}

#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
#[ignore_extra_doc_attributes]
pub enum MatchResult {
  /// Continue matching.
  Continue = 0,
  /// Immediately cease matching.
  ///
  /// If scanning is performed in streaming mode and this value is returned, any
  /// subsequent calls to
  /// [`Scratch::scan_sync_stream()`](crate::state::Scratch::scan_sync_stream)
  /// or [`Scratch::scan_stream()`](crate::state::Scratch::scan_stream)
  /// for the same stream will immediately return with
  /// [`ScanTerminated`](crate::error::HyperscanRuntimeError::ScanTerminated).
  CeaseMatching = 1,
}

impl MatchResult {
  pub(crate) const fn into_native(self) -> c_int {
    match self {
      Self::Continue => 0,
      /* This is documented to be just any non-zero value at the moment. */
      Self::CeaseMatching => 1,
    }
  }
}

#[derive(Debug)]
pub(crate) struct MatchEvent {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub context: Option<ptr::NonNull<c_void>>,
}

impl MatchEvent {
  pub fn coerce_args(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> Self {
    static_assertions::assert_eq_size!(c_uint, ExpressionIndex);
    debug_assert_eq!(flags, 0, "flags are currently unused");
    Self {
      id: ExpressionIndex(id),
      range: RangeIndex::bounded_range(RangeIndex(from), RangeIndex(to)),
      context: ptr::NonNull::new(context),
    }
  }

  pub unsafe fn extract_context<'a, T>(
    context: Option<ptr::NonNull<c_void>>,
  ) -> Option<Pin<&'a mut T>> {
    context.map(|c| Pin::new_unchecked(&mut *mem::transmute::<*mut c_void, *mut T>(c.as_ptr())))
  }
}

pub mod contiguous_slice {
  use super::*;

  #[derive(Debug)]
  pub struct Match<'a> {
    pub id: ExpressionIndex,
    pub source: ByteSlice<'a>,
  }

  pub(crate) struct SliceMatcher<'data, 'code> {
    parent_slice: ByteSlice<'data>,
    handler: &'code mut (dyn FnMut(Match<'data>) -> MatchResult),
  }

  impl<'data, 'code> SliceMatcher<'data, 'code> {
    pub fn new<F: FnMut(Match<'data>) -> MatchResult>(
      parent_slice: ByteSlice<'data>,
      f: &'code mut F,
    ) -> Self {
      Self {
        parent_slice,
        handler: f,
      }
    }

    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    pub fn handle_match(&mut self, m: Match<'data>) -> MatchResult { (self.handler)(m) }
  }

  pub(crate) unsafe extern "C" fn match_slice(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, flags, context);
    let mut sync_slice_matcher: Pin<&mut SliceMatcher> =
      MatchEvent::extract_context(context).unwrap();
    let matched_substring = sync_slice_matcher.index_range(range);
    let m = Match {
      id,
      source: matched_substring,
    };

    let result = sync_slice_matcher.handle_match(m);
    result.into_native()
  }

  /* TODO: only available on nightly! */
  /* pub trait Scanner<'data> = FnMut(&Match<'data>) -> MatchResult; */
}

pub mod vectored_slice {
  use super::*;

  #[derive(Debug)]
  pub struct VectoredMatch<'a> {
    pub id: ExpressionIndex,
    pub source: Vec<ByteSlice<'a>>,
  }

  pub(crate) struct VectoredMatcher<'data, 'code> {
    parent_slices: VectoredByteSlices<'data>,
    handler: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult),
  }

  impl<'data, 'code> VectoredMatcher<'data, 'code> {
    pub fn new<F: FnMut(VectoredMatch<'data>) -> MatchResult>(
      parent_slices: VectoredByteSlices<'data>,
      f: &'code mut F,
    ) -> Self {
      Self {
        parent_slices,
        handler: f,
      }
    }

    pub fn parent_slices(&self) -> VectoredByteSlices<'data> { self.parent_slices }

    pub fn index_range(&self, range: ops::Range<usize>) -> Vec<ByteSlice<'data>> {
      self.parent_slices.index_range(range).unwrap()
    }

    pub fn handle_match(&mut self, m: VectoredMatch<'data>) -> MatchResult { (self.handler)(m) }
  }

  pub(crate) unsafe extern "C" fn match_slice_vectored(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, flags, context);
    let mut sync_slice_matcher: Pin<&mut VectoredMatcher> =
      MatchEvent::extract_context(context).unwrap();
    let matched_substring = sync_slice_matcher.index_range(range);
    let m = VectoredMatch {
      id,
      source: matched_substring,
    };

    let result = sync_slice_matcher.handle_match(m);
    result.into_native()
  }

  /* TODO: only available on nightly! */
  /* pub trait VectorScanner<'data> = FnMut(&VectoredMatch<'data>) ->
   * MatchResult; */
}

pub mod stream {
  use super::*;

  #[cfg(feature = "async")]
  use tokio::sync::mpsc;

  // ///```
  // /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  // tokio_test::block_on(async { /// use hyperscan::{expression::*,
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
  #[derive(Debug)]
  pub struct StreamMatch {
    pub id: ExpressionIndex,
    pub range: ops::Range<usize>,
  }

  pub trait StreamHandler {
    fn handle_match(&mut self, m: StreamMatch) -> MatchResult;

    fn new() -> Self
    where Self: Sized;

    fn reset(&mut self);
    fn boxed_clone(&self) -> Box<dyn StreamHandler>;
  }

  pub struct StreamMatcher {
    handler: Box<dyn StreamHandler>,
  }

  impl StreamMatcher {
    pub fn new<S: StreamHandler+'static>() -> Self {
      Self {
        handler: Box::new(S::new()),
      }
    }

    pub fn handle_match(&mut self, m: StreamMatch) -> MatchResult { self.handler.handle_match(m) }

    pub fn reset(&mut self) { self.handler.reset(); }
  }

  impl Clone for StreamMatcher {
    fn clone(&self) -> Self {
      Self {
        handler: self.handler.boxed_clone(),
      }
    }
  }

  pub(crate) unsafe extern "C" fn match_slice_stream(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, flags, context);
    let mut matcher: Pin<&mut StreamMatcher> = MatchEvent::extract_context(context).unwrap();

    let m = StreamMatch { id, range };

    let result = matcher.handle_match(m);
    result.into_native()
  }

  #[cfg(feature = "async")]
  #[cfg_attr(docsrs, doc(cfg(feature = "async")))]
  pub mod scan {
    use super::*;

    pub trait StreamScanner: Send+Sync {
      fn scan_match(&mut self, m: &StreamMatch) -> MatchResult;

      fn new() -> Self
      where Self: Sized;

      fn reset(&mut self);
      fn boxed_clone(&self) -> Box<dyn StreamScanner>;
    }

    pub struct TrivialScanner;
    impl StreamScanner for TrivialScanner {
      fn scan_match(&mut self, _m: &StreamMatch) -> MatchResult { MatchResult::Continue }

      fn new() -> Self
      where Self: Sized {
        Self
      }

      fn reset(&mut self) {}
      fn boxed_clone(&self) -> Box<dyn StreamScanner> { Box::new(Self) }
    }

    pub struct StreamScanMatcher {
      sender: mpsc::UnboundedSender<StreamMatch>,
      scanner: Box<dyn StreamScanner>,
    }

    impl StreamScanMatcher {
      pub fn new<S: StreamScanner+'static>(sender: mpsc::UnboundedSender<StreamMatch>) -> Self {
        Self {
          sender,
          scanner: Box::new(S::new()),
        }
      }

      pub fn scan_match(&mut self, m: &StreamMatch) -> MatchResult { self.scanner.scan_match(m) }

      pub fn push_match(&mut self, m: StreamMatch) { self.sender.send(m).unwrap(); }

      pub fn reset(&mut self) { self.scanner.reset(); }

      pub fn replace_sender(
        &mut self,
        sender: mpsc::UnboundedSender<StreamMatch>,
      ) -> mpsc::UnboundedSender<StreamMatch> {
        mem::replace(&mut self.sender, sender)
      }

      pub fn clone_with_sender(&self, sender: mpsc::UnboundedSender<StreamMatch>) -> Self {
        Self {
          sender,
          scanner: self.scanner.boxed_clone(),
        }
      }
    }

    impl Clone for StreamScanMatcher {
      fn clone(&self) -> Self { self.clone_with_sender(self.sender.clone()) }
    }

    pub(crate) unsafe extern "C" fn scan_slice_stream(
      id: c_uint,
      from: c_ulonglong,
      to: c_ulonglong,
      flags: c_uint,
      context: *mut c_void,
    ) -> c_int {
      let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, flags, context);
      let mut matcher: Pin<&mut StreamScanMatcher> = MatchEvent::extract_context(context).unwrap();

      let m = StreamMatch { id, range };

      let result = matcher.scan_match(&m);
      matcher.push_match(m);
      result.into_native()
    }
  }
}

#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;
  use crate::{error::chimera::*, hs};

  use displaydoc::Display;

  use std::{
    ffi::{c_uint, c_ulonglong, c_void},
    ops,
    pin::Pin,
    ptr, slice,
  };

  #[derive(
    Debug,
    Display,
    Copy,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    num_enum::TryFromPrimitive,
    num_enum::IntoPrimitive,
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
    pub(crate) fn into_native(self) -> hs::ch_callback_t {
      let x: u8 = self.into();
      x.into()
    }
  }

  #[derive(Debug)]
  struct ChimeraMatchEvent<'a> {
    pub id: ExpressionIndex,
    pub range: ops::Range<usize>,
    pub captures: &'a [hs::ch_capture],
    pub context: Option<ptr::NonNull<c_void>>,
  }

  impl<'a> ChimeraMatchEvent<'a> {
    pub fn coerce_args(
      id: c_uint,
      from: c_ulonglong,
      to: c_ulonglong,
      flags: c_uint,
      size: c_uint,
      captured: *const hs::ch_capture,
      context: *mut c_void,
    ) -> Self {
      debug_assert_eq!(flags, 0, "flags are currently unused");
      Self {
        id: ExpressionIndex(id),
        range: RangeIndex::bounded_range(RangeIndex(from), RangeIndex(to)),
        captures: unsafe { slice::from_raw_parts(captured, size as usize) },
        context: ptr::NonNull::new(context),
      }
    }

    pub unsafe fn extract_context<'c, T>(
      context: Option<ptr::NonNull<c_void>>,
    ) -> Option<Pin<&'c mut T>> {
      MatchEvent::extract_context(context)
    }
  }

  #[derive(Debug)]
  pub struct ChimeraMatch<'a> {
    pub id: ExpressionIndex,
    pub source: ByteSlice<'a>,
    pub captures: Vec<Option<ByteSlice<'a>>>,
  }

  pub(crate) struct ChimeraSyncSliceMatcher<'data, 'code> {
    parent_slice: ByteSlice<'data>,
    match_handler: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult),
    error_handler: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult),
  }

  impl<'data, 'code> ChimeraSyncSliceMatcher<'data, 'code> {
    pub fn new(
      parent_slice: ByteSlice<'data>,
      matcher: &'code mut impl FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult,
      error: &'code mut impl FnMut(ChimeraMatchError) -> ChimeraMatchResult,
    ) -> Self {
      Self {
        parent_slice,
        match_handler: matcher,
        error_handler: error,
      }
    }

    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    pub fn handle_match(&mut self, m: ChimeraMatch<'data>) -> ChimeraMatchResult {
      (self.match_handler)(m)
    }

    pub fn handle_error(&mut self, e: ChimeraMatchError) -> ChimeraMatchResult {
      (self.error_handler)(e)
    }
  }

  pub(crate) unsafe extern "C" fn match_chimera_slice(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    size: c_uint,
    captured: *const hs::ch_capture,
    context: *mut c_void,
  ) -> hs::ch_callback_t {
    let ChimeraMatchEvent {
      id,
      range,
      captures,
      context,
    } = ChimeraMatchEvent::coerce_args(id, from, to, flags, size, captured, context);
    let mut matcher: Pin<&mut ChimeraSyncSliceMatcher> =
      ChimeraMatchEvent::extract_context(context).unwrap();
    let matched_substring = matcher.index_range(range);
    let m = ChimeraMatch {
      id,
      source: matched_substring,
      captures: captures
        .iter()
        .map(|hs::ch_capture { flags, from, to }| {
          if *flags == hs::CH_CAPTURE_FLAG_INACTIVE as c_uint {
            None
          } else {
            debug_assert_eq!(*flags, hs::CH_CAPTURE_FLAG_ACTIVE as c_uint);
            let range = RangeIndex::bounded_range(RangeIndex(*from), RangeIndex(*to));
            Some(matcher.index_range(range))
          }
        })
        .collect(),
    };

    let result = matcher.handle_match(m);
    result.into_native()
  }

  pub(crate) unsafe extern "C" fn error_callback_chimera(
    error_type: hs::ch_error_event_t,
    id: c_uint,
    info: *mut c_void,
    ctx: *mut c_void,
  ) -> hs::ch_callback_t {
    let error_type = ChimeraMatchErrorType::from_native(error_type);
    let id = ExpressionIndex(id);
    debug_assert!(info.is_null(), "info pointer is currently unused");
    let ctx = ptr::NonNull::new(ctx);
    let mut matcher: Pin<&mut ChimeraSyncSliceMatcher> =
      ChimeraMatchEvent::extract_context(ctx).unwrap();
    let e = ChimeraMatchError { error_type, id };

    let result = matcher.handle_error(e);
    result.into_native()
  }
}

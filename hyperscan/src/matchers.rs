/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::flags::ScanFlags;

use displaydoc::Display;
use tokio::sync::mpsc;

use std::{
  cmp, mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr, slice, str,
};

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct ByteSlice<'a>(&'a [u8]);

impl<'a> ByteSlice<'a> {
  #[inline(always)]
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.0.get(range).map(Self)
  }

  #[inline(always)]
  pub const fn from_str(data: &'a str) -> Self { Self(data.as_bytes()) }

  #[inline(always)]
  pub const fn from_slice(data: &'a [u8]) -> Self { Self(data) }

  #[inline(always)]
  pub const fn as_slice(&self) -> &'a [u8] { unsafe { mem::transmute(self.0) } }

  #[inline(always)]
  pub const fn as_str(&self) -> &'a str { unsafe { str::from_utf8_unchecked(self.as_slice()) } }

  #[inline(always)]
  pub(crate) const fn as_ptr(&self) -> *const c_char { unsafe { mem::transmute(self.0.as_ptr()) } }

  #[inline(always)]
  pub const fn len(&self) -> usize { self.0.len() }

  #[inline(always)]
  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  #[inline(always)]
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
  #[inline(always)]
  pub const fn from_slices(data: &'a [ByteSlice<'a>]) -> Self { Self(data) }

  #[inline(always)]
  pub(crate) fn pointers_and_lengths(&self) -> (Vec<*const c_char>, Vec<c_uint>) {
    let lengths: Vec<c_uint> = self.0.iter().map(|col| col.native_len()).collect();
    let data_pointers: Vec<*const c_char> = self.0.iter().map(|col| col.as_ptr()).collect();
    (data_pointers, lengths)
  }

  #[inline(always)]
  pub const fn len(&self) -> usize { self.0.len() }

  #[inline(always)]
  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  #[inline(always)]
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

/// <expression index {0}>
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub c_uint);

/// <range index {0}>
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
struct RangeIndex(pub c_ulonglong);

impl RangeIndex {
  #[inline(always)]
  pub const fn into_rust_index(self) -> usize {
    static_assertions::const_assert!(mem::size_of::<usize>() >= mem::size_of::<c_ulonglong>());
    self.0 as usize
  }

  #[inline(always)]
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
  /// subsequent calls to @ref hs_scan_stream() for the same stream will
  /// immediately return with
  /// [`SCAN_TERMINATED`](crate::error::HyperscanError::ScanTerminated).
  CeaseMatching = 1,
}

impl MatchResult {
  /* FIXME: update num_enum so they work with const fn too!!! */
  #[inline(always)]
  #[allow(dead_code)]
  pub(crate) const fn from_native(x: c_int) -> Self {
    if x == 0 {
      Self::Continue
    } else {
      Self::CeaseMatching
    }
  }

  #[inline(always)]
  pub(crate) const fn into_native(self) -> c_int {
    match self {
      Self::Continue => 0,
      Self::CeaseMatching => 1,
    }
  }
}

#[derive(Debug)]
pub(crate) struct MatchEvent {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub flags: ScanFlags,
  pub context: Option<ptr::NonNull<c_void>>,
}

impl MatchEvent {
  #[inline(always)]
  pub fn coerce_args(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> Self {
    static_assertions::assert_eq_size!(c_uint, ExpressionIndex);
    Self {
      id: ExpressionIndex(id),
      range: RangeIndex::bounded_range(RangeIndex(from), RangeIndex(to)),
      flags: ScanFlags::from_native(flags),
      context: ptr::NonNull::new(context),
    }
  }

  #[inline(always)]
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
    pub flags: ScanFlags,
  }

  /* TODO: only available on nightly! */
  /* pub trait Scanner<'data> = FnMut(&Match<'data>) -> MatchResult+'data; */

  pub(crate) struct SliceMatcher<'data, 'code> {
    parent_slice: ByteSlice<'data>,
    matches_tx: mpsc::UnboundedSender<Match<'data>>,
    handler: &'code mut (dyn FnMut(&Match<'data>) -> MatchResult+'data),
  }

  impl<'data, 'code> SliceMatcher<'data, 'code> {
    #[inline]
    pub fn new<F: FnMut(&Match<'data>) -> MatchResult+'data>(
      parent_slice: ByteSlice<'data>,
      f: &'code mut F,
    ) -> (Self, mpsc::UnboundedReceiver<Match<'data>>) {
      let (matches_tx, matches_rx) = mpsc::unbounded_channel();
      let s = Self {
        parent_slice,
        matches_tx,
        handler: f,
      };
      (s, matches_rx)
    }

    #[inline]
    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    #[inline(always)]
    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    #[inline(always)]
    pub fn push_new_match(&self, m: Match<'data>) { self.matches_tx.send(m).unwrap(); }

    #[inline(always)]
    pub fn handle_match(&mut self, m: &Match<'data>) -> MatchResult { (self.handler)(m) }
  }

  pub(crate) unsafe extern "C" fn match_slice_ref(
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
    let mut slice_matcher: Pin<&mut SliceMatcher> =
      MatchEvent::extract_context::<'_, SliceMatcher>(context).unwrap();
    let matched_substring = slice_matcher.index_range(range);
    let m = Match {
      id,
      source: matched_substring,
      flags,
    };

    let result = slice_matcher.handle_match(&m);
    slice_matcher.push_new_match(m);
    result.into_native()
  }
}

pub mod vectored_slice {
  use super::*;

  #[derive(Debug)]
  pub struct VectoredMatch<'a> {
    pub id: ExpressionIndex,
    pub source: Vec<ByteSlice<'a>>,
    pub flags: ScanFlags,
  }

  /* TODO: only available on nightly! */
  /* pub trait VectorScanner<'data> = FnMut(&VectoredMatch<'data>) ->
   * MatchResult+'data; */

  pub(crate) struct VectoredSliceMatcher<'data, 'code> {
    parent_slices: VectoredByteSlices<'data>,
    matches_tx: mpsc::UnboundedSender<VectoredMatch<'data>>,
    handler: &'code mut (dyn FnMut(&VectoredMatch<'data>) -> MatchResult+'data),
  }

  impl<'data, 'code> VectoredSliceMatcher<'data, 'code> {
    #[inline]
    pub fn new<F: FnMut(&VectoredMatch<'data>) -> MatchResult+'data>(
      parent_slices: VectoredByteSlices<'data>,
      f: &'code mut F,
    ) -> (Self, mpsc::UnboundedReceiver<VectoredMatch<'data>>) {
      let (matches_tx, matches_rx) = mpsc::unbounded_channel();
      let s = Self {
        parent_slices,
        matches_tx,
        handler: f,
      };
      (s, matches_rx)
    }

    pub fn parent_slices(&self) -> VectoredByteSlices<'data> { self.parent_slices }

    pub fn index_range(&self, range: ops::Range<usize>) -> Vec<ByteSlice<'data>> {
      self.parent_slices.index_range(range).unwrap()
    }

    #[inline(always)]
    pub fn push_new_match(&mut self, m: VectoredMatch<'data>) { self.matches_tx.send(m).unwrap(); }

    #[inline(always)]
    pub fn handle_match(&mut self, m: &VectoredMatch<'data>) -> MatchResult { (self.handler)(m) }
  }

  pub(crate) unsafe extern "C" fn match_slice_vectored_ref(
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
    let mut slice_matcher: Pin<&mut VectoredSliceMatcher> =
      MatchEvent::extract_context::<'_, VectoredSliceMatcher>(context).unwrap();
    let matched_substring = slice_matcher.index_range(range);
    let m = VectoredMatch {
      id,
      source: matched_substring,
      flags,
    };

    let result = slice_matcher.handle_match(&m);
    slice_matcher.push_new_match(m);
    result.into_native()
  }
}

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
    #[inline(always)]
    pub(crate) fn into_native(self) -> hs::ch_callback_t {
      let x: u8 = self.into();
      x.into()
    }
  }

  #[derive(Debug, Clone, PartialEq, Eq, Hash)]
  enum ChimeraCaptureOffset {
    Active(ops::Range<usize>),
    Inactive,
  }

  impl ChimeraCaptureOffset {
    pub fn index<'a>(self, source: ByteSlice<'a>) -> Option<ByteSlice<'a>> {
      match self {
        Self::Inactive => None,
        Self::Active(range) => source.index_range(range),
      }
    }
  }

  #[derive(Debug)]
  struct ChimeraMatchEvent {
    pub id: ExpressionIndex,
    pub range: ops::Range<usize>,
    pub flags: ScanFlags,
    pub captures: Vec<ChimeraCaptureOffset>,
    pub context: Option<ptr::NonNull<c_void>>,
  }

  impl ChimeraMatchEvent {
    #[inline(always)]
    pub fn coerce_args(
      id: c_uint,
      from: c_ulonglong,
      to: c_ulonglong,
      flags: c_uint,
      size: c_uint,
      captured: *const hs::ch_capture,
      context: *mut c_void,
    ) -> Self {
      let captures: Vec<ChimeraCaptureOffset> =
        unsafe { slice::from_raw_parts(captured, size as usize) }
          .iter()
          .map(|hs::ch_capture { flags, from, to }| {
            if *flags == hs::CH_CAPTURE_FLAG_INACTIVE as c_uint {
              ChimeraCaptureOffset::Inactive
            } else {
              assert_eq!(*flags, hs::CH_CAPTURE_FLAG_ACTIVE as c_uint);
              ChimeraCaptureOffset::Active(RangeIndex::bounded_range(
                RangeIndex(*from),
                RangeIndex(*to),
              ))
            }
          })
          .collect();
      Self {
        id: ExpressionIndex(id),
        range: RangeIndex::bounded_range(RangeIndex(from), RangeIndex(to)),
        flags: ScanFlags::from_native(flags),
        captures,
        context: ptr::NonNull::new(context),
      }
    }

    #[inline(always)]
    pub unsafe fn extract_context<'a, T>(
      context: Option<ptr::NonNull<c_void>>,
    ) -> Option<Pin<&'a mut T>> {
      MatchEvent::extract_context(context)
    }
  }

  #[derive(Debug)]
  pub struct ChimeraMatch<'a> {
    pub id: ExpressionIndex,
    pub source: ByteSlice<'a>,
    pub flags: ScanFlags,
    pub captures: Vec<Option<ByteSlice<'a>>>,
  }

  pub trait ChimeraScanner<'data> {
    fn handle_match(&mut self, m: &ChimeraMatch<'data>) -> ChimeraMatchResult;
    fn handle_error(&mut self, e: &ChimeraMatchError) -> ChimeraMatchResult;
    fn new() -> Self
    where Self: Sized;
  }

  pub struct TrivialChimeraScanner;

  impl<'data> ChimeraScanner<'data> for TrivialChimeraScanner {
    fn handle_match(&mut self, _m: &ChimeraMatch<'data>) -> ChimeraMatchResult {
      ChimeraMatchResult::Continue
    }

    fn handle_error(&mut self, _e: &ChimeraMatchError) -> ChimeraMatchResult {
      ChimeraMatchResult::Continue
    }

    fn new() -> Self
    where Self: Sized {
      Self
    }
  }

  pub(crate) struct ChimeraSliceMatcher<'data, 'code> {
    parent_slice: ByteSlice<'data>,
    matches_tx: mpsc::UnboundedSender<ChimeraMatch<'data>>,
    errors_tx: mpsc::UnboundedSender<ChimeraMatchError>,
    handler: &'code mut dyn ChimeraScanner<'data>,
  }

  impl<'data, 'code> ChimeraSliceMatcher<'data, 'code> {
    #[inline]
    pub fn new(
      parent_slice: ByteSlice<'data>,
      scanner: &'code mut impl ChimeraScanner<'data>,
    ) -> (
      Self,
      mpsc::UnboundedReceiver<ChimeraMatch<'data>>,
      mpsc::UnboundedReceiver<ChimeraMatchError>,
    ) {
      let (matches_tx, matches_rx) = mpsc::unbounded_channel();
      let (errors_tx, errors_rx) = mpsc::unbounded_channel();
      let s = Self {
        parent_slice,
        matches_tx,
        errors_tx,
        handler: scanner,
      };
      (s, matches_rx, errors_rx)
    }

    #[inline]
    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    #[inline(always)]
    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    #[inline(always)]
    pub fn push_new_match(&self, m: ChimeraMatch<'data>) { self.matches_tx.send(m).unwrap(); }

    #[inline(always)]
    pub fn handle_match(&mut self, m: &ChimeraMatch<'data>) -> ChimeraMatchResult {
      self.handler.handle_match(m)
    }

    #[inline(always)]
    pub fn push_new_error(&self, e: ChimeraMatchError) { self.errors_tx.send(e).unwrap(); }

    #[inline(always)]
    pub fn handle_error(&mut self, e: &ChimeraMatchError) -> ChimeraMatchResult {
      self.handler.handle_error(e)
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
      flags,
      captures,
      context,
    } = ChimeraMatchEvent::coerce_args(id, from, to, flags, size, captured, context);
    let mut matcher: Pin<&mut ChimeraSliceMatcher<'_, '_>> =
      ChimeraMatchEvent::extract_context::<'_, ChimeraSliceMatcher<'_, '_>>(context).unwrap();
    let matched_substring = matcher.index_range(range);
    let m = ChimeraMatch {
      id,
      source: matched_substring,
      flags,
      captures: captures
        .into_iter()
        .map(|c| c.index(matcher.parent_slice()))
        .collect(),
    };

    let result = matcher.handle_match(&m);
    /* TODO: do we want to make configurable whether SkipPattern still forwards
     * the match to the channel? */
    matcher.push_new_match(m);
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
    let info = ptr::NonNull::new(info);
    let ctx = ptr::NonNull::new(ctx);
    let mut matcher: Pin<&mut ChimeraSliceMatcher<'_, '_>> =
      ChimeraMatchEvent::extract_context::<'_, ChimeraSliceMatcher<'_, '_>>(ctx).unwrap();
    let e = ChimeraMatchError {
      error_type,
      id,
      info,
    };

    let result = matcher.handle_error(&e);
    matcher.push_new_error(e);
    result.into_native()
  }
}

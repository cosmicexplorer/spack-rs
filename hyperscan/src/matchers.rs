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
pub struct ByteSlice<'a>(pub &'a [u8]);

impl<'a> ByteSlice<'a> {
  #[inline(always)]
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.0.get(range).map(Self)
  }

  #[inline(always)]
  pub(crate) const fn as_ptr(&self) -> *const c_char { unsafe { mem::transmute(self.0.as_ptr()) } }

  #[inline(always)]
  pub const fn len(&self) -> usize { self.0.len() }

  #[inline(always)]
  pub(crate) const fn native_len(&self) -> c_uint { self.len() as c_uint }

  #[inline]
  pub fn decode_utf8(&self) -> Result<&'a str, str::Utf8Error> { str::from_utf8(&self.0) }
}

impl<'a> From<&'a [u8]> for ByteSlice<'a> {
  fn from(x: &'a [u8]) -> Self { Self(x) }
}

impl<'a, const N: usize> From<&'a [u8; N]> for ByteSlice<'a> {
  fn from(x: &'a [u8; N]) -> Self { Self(x.as_ref()) }
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct VectoredByteSlices<'a>(pub &'a [ByteSlice<'a>]);

impl<'a> VectoredByteSlices<'a> {
  #[inline(always)]
  pub(crate) fn pointers_and_lengths(&self) -> (Vec<*const c_char>, Vec<c_uint>) {
    let lengths: Vec<c_uint> = self.0.iter().map(|col| col.len() as c_uint).collect();
    let data_pointers: Vec<*const c_char> = self.0.iter().map(|col| col.as_ptr()).collect();
    (data_pointers, lengths)
  }

  #[inline(always)]
  pub const fn len(&self) -> usize { self.0.len() }

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
    let (end_col, end_ind) = self.find_index_at(start_col, start_ind, end)?;
    self.collect_slices_range((start_col, start_ind), (end_col, end_ind))
  }
}

impl<'a> From<&'a [ByteSlice<'a>]> for VectoredByteSlices<'a> {
  fn from(x: &'a [ByteSlice<'a>]) -> Self { Self(x) }
}

impl<'a> From<&'a [&'a [u8]]> for VectoredByteSlices<'a> {
  fn from(x: &'a [&'a [u8]]) -> Self {
    let x: &'a [ByteSlice<'a>] = unsafe { mem::transmute(x) };
    Self(x)
  }
}

/// <expression index {0}>
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub c_uint);

impl ExpressionIndex {
  pub const WHOLE_PATTERN: Self = Self(0);
}

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
  /// [`SCAN_TERMINATED`](HyperscanError::ScanTerminated).
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
  pub const fn coerce_args(
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
  pub const unsafe fn extract_context<'a, T>(
    context: Option<ptr::NonNull<c_void>>,
  ) -> Option<Pin<&'a mut T>> {
    match context {
      None => None,
      Some(c) => Some(Pin::new_unchecked(&mut *mem::transmute::<
        *mut c_void,
        *mut T,
      >(c.as_ptr()))),
    }
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

  pub trait Scanner<'data> = FnMut(&Match<'data>) -> MatchResult+'data;

  pub(crate) struct SliceMatcher<'data, 'code> {
    parent_slice: ByteSlice<'data>,
    matches_tx: mpsc::Sender<Match<'data>>,
    handler: &'code mut dyn Scanner<'data>,
  }

  impl<'data, 'code> SliceMatcher<'data, 'code> {
    #[inline]
    pub fn new<const N: usize, F: Scanner<'data>>(
      parent_slice: ByteSlice<'data>,
      f: &'code mut F,
    ) -> (Self, mpsc::Receiver<Match<'data>>) {
      let (matches_tx, matches_rx) = mpsc::channel(N);
      let s = Self {
        parent_slice,
        matches_tx,
        handler: f,
      };
      (s, matches_rx)
    }

    #[inline]
    pub(crate) fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    #[inline(always)]
    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    #[inline(always)]
    pub fn push_new_match(&self, m: Match<'data>) { self.matches_tx.blocking_send(m).unwrap(); }

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
    dbg!(m.source.decode_utf8().unwrap());

    let result = slice_matcher.handle_match(&m);
    if result == MatchResult::Continue {
      slice_matcher.push_new_match(m);
    }

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

  pub trait VectorScanner<'data> = FnMut(&VectoredMatch<'data>) -> MatchResult+'data;

  pub(crate) struct VectoredSliceMatcher<'data, 'code> {
    parent_slices: VectoredByteSlices<'data>,
    matches_tx: mpsc::Sender<VectoredMatch<'data>>,
    handler: &'code mut dyn VectorScanner<'data>,
  }

  impl<'data, 'code> VectoredSliceMatcher<'data, 'code> {
    #[inline]
    pub fn new<const N: usize, F: VectorScanner<'data>>(
      parent_slices: VectoredByteSlices<'data>,
      f: &'code mut F,
    ) -> (Self, mpsc::Receiver<VectoredMatch<'data>>) {
      let (matches_tx, matches_rx) = mpsc::channel(N);
      let s = Self {
        parent_slices,
        matches_tx,
        handler: f,
      };
      (s, matches_rx)
    }

    pub(crate) fn parent_slices(&self) -> VectoredByteSlices<'data> { self.parent_slices }

    pub fn index_range(&self, range: ops::Range<usize>) -> Vec<ByteSlice<'data>> {
      self.parent_slices.index_range(range).unwrap()
    }

    #[inline(always)]
    pub fn push_new_match(&mut self, m: VectoredMatch<'data>) {
      self.matches_tx.blocking_send(m).unwrap();
    }

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
    eprintln!("oh dear!");
    let mut slice_matcher: Pin<&mut VectoredSliceMatcher> =
      MatchEvent::extract_context::<'_, VectoredSliceMatcher>(context).unwrap();
    let matched_substring = slice_matcher.index_range(range);
    let m = VectoredMatch {
      id,
      source: matched_substring,
      flags,
    };
    dbg!(&m);
    dbg!(m
      .source
      .iter()
      .map(|s| s.decode_utf8().unwrap())
      .collect::<Vec<_>>());

    let result = slice_matcher.handle_match(&m);
    if result == MatchResult::Continue {
      slice_matcher.push_new_match(m);
    }

    result.into_native()
  }
}

/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Wrappers for types of string data which can be searched and indexed.
//!
//! These objects are used to provide string data for inputs to search functions
//! like [`scan_sync()`](crate::state::Scratch::scan_sync), and subsets of those
//! arguments are received as outputs by match callbacks to produce match info
//! such as [`Match`](crate::matchers::contiguous_slice::Match).

use std::{
  cmp, mem, ops,
  os::raw::{c_char, c_uint},
  slice, str,
};

/// A [`slice`](prim@slice) of [`u8`] with an associated lifetime.
#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct ByteSlice<'a>(&'a [u8]);

/// # Byte-Oriented Interface
/// Hyperscan can search over arbitrary byte patterns in any encoding, so
/// [`Self::from_slice()`] and [`Self::as_slice()`] offer the most general
/// byte-oriented interface. This may be particularly useful when matching
/// against non-UTF8 data, possibly with [`Literal`](crate::expression::Literal)
/// pattern strings (although non-literal patterns can also be used to
/// match non-UTF8 data).
///
/// [`From`] implementations are also provided to convert from native
/// [arrays](prim@array) and [slices](prim@slice).
impl<'a> ByteSlice<'a> {
  pub const fn from_slice(data: &'a [u8]) -> Self { Self(data) }

  pub const fn as_slice(&self) -> &'a [u8] { self.0 }

  pub(crate) const fn as_ptr(&self) -> *const c_char { self.as_slice().as_ptr() as *const c_char }

  pub(crate) const fn native_len(&self) -> c_uint { self.as_slice().len() as c_uint }
}

impl<'a> From<&'a [u8]> for ByteSlice<'a> {
  fn from(x: &'a [u8]) -> Self { Self::from_slice(x) }
}

impl<'a, const N: usize> From<&'a [u8; N]> for ByteSlice<'a> {
  fn from(x: &'a [u8; N]) -> Self { Self::from_slice(x.as_ref()) }
}

/// # String-Oriented Interface
/// When hyperscan is being used with UTF8-encoded inputs (e.g. with
/// [`Self::from_str()`]), it will produce UTF8 encoded match outputs, and
/// [`Self::as_str()`] can be invoked safely on match results.
///
/// A [`From`] implementation is also provided to convert from a native
/// [`str`](prim@str).
///
/// ## The `UTF8` Flag
/// It is important to note that hyperscan itself does not assume any particular
/// string encoding, and the function of e.g.
/// [`Flags::UTF8`](crate::flags::Flags::UTF8) is to determine which bytes
/// should be included in the state machine, *not* the encoding of any
/// particular input. This means that the UTF8 flag may be disabled for UTF8
/// inputs to produce a much smaller state machine (as it is when using
/// [`Flags::default()`](crate::flags::Flags::default)). Note however that
/// enabling the UTF8 flag for non-UTF8 inputs produces undefined behavior.
impl<'a> ByteSlice<'a> {
  pub const fn from_str(data: &'a str) -> Self { Self::from_slice(data.as_bytes()) }

  pub const unsafe fn as_str(&self) -> &'a str { str::from_utf8_unchecked(self.as_slice()) }
}

impl<'a> From<&'a str> for ByteSlice<'a> {
  fn from(x: &'a str) -> Self { Self::from_str(x) }
}

/// # Subsetting
/// Match callbacks return subsets of the input argument. These methods apply a
/// fallible subsetting operation which is used to convert match offsets to
/// substrings.
impl<'a> ByteSlice<'a> {
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.as_slice().get(range).map(Self::from_slice)
  }
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

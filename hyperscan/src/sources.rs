/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use std::{
  cmp, mem, ops,
  os::raw::{c_char, c_uint},
  slice, str,
};

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct ByteSlice<'a>(&'a [u8]);

impl<'a> ByteSlice<'a> {
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.as_slice().get(range).map(Self::from_slice)
  }

  pub const fn from_str(data: &'a str) -> Self { Self::from_slice(data.as_bytes()) }

  pub const fn from_slice(data: &'a [u8]) -> Self { Self(data) }

  pub const fn as_slice(&self) -> &'a [u8] { self.0 }

  pub const unsafe fn as_str(&self) -> &'a str { str::from_utf8_unchecked(self.as_slice()) }

  pub(crate) const fn as_ptr(&self) -> *const c_char { self.as_slice().as_ptr() as *const c_char }

  pub const fn len(&self) -> usize { self.as_slice().len() }

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

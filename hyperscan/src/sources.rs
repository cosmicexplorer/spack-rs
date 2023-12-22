/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Wrappers for types of string data which can be searched and indexed.
//!
//! These objects are used to provide string data for inputs to search functions
//! like [`scan_sync()`](crate::state::Scratch::scan_sync), and subsets of those
//! arguments are received as outputs by match callbacks to produce match info
//! such as [`Match`](crate::matchers::contiguous_slice::Match).

use std::{
  cmp, fmt, mem, ops,
  os::raw::{c_char, c_uint},
  slice, str,
};

/// A [`slice`](prim@slice) of [`u8`] with an associated lifetime.
///
/// This is currently implemented as
/// a [`#[repr(transparent)]`](https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent)
/// wrapper over `&'a [u8]`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ByteSlice<'a>(&'a [u8]);

impl<'a> fmt::Debug for ByteSlice<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let b = self.as_slice();
    match str::from_utf8(b) {
      Ok(s) => write!(f, "ByteSlice({:?})", s),
      Err(_) => write!(f, "ByteSlice(non-utf8: {:?})", b),
    }
  }
}

impl<'a> fmt::Display for ByteSlice<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let b = self.as_slice();
    match str::from_utf8(b) {
      Ok(s) => write!(f, "{}", s),
      Err(_) => write!(f, "(non-utf8: {:?})", b),
    }
  }
}

/// # Byte-Oriented Interface
/// Hyperscan can search over arbitrary byte patterns in any encoding, so
/// [`Self::from_slice()`] and [`Self::as_slice()`] offer the most general
/// byte-oriented interface. This may be particularly useful when matching
/// against non-UTF8 data, possibly with [`Literal`](crate::expression::Literal)
/// pattern strings (although non-literal patterns can also be used to
/// match non-UTF8 data).
///
/// [`From`] implementations are also provided to convert from references to
/// native [arrays](prim@array) and [slices](prim@slice):
///
///```
/// use hyperscan::sources::ByteSlice;
///
/// let b1 = ByteSlice::from_slice(b"asdf");
/// let b2: ByteSlice = b"asdf".into();
/// let b3: ByteSlice = ['a' as u8, 's' as u8, 'd' as u8, 'f' as u8].as_ref().into();
/// assert_eq!(b1, b2);
/// assert_eq!(b2, b3);
/// assert_eq!(b1.as_slice(), b"asdf");
/// ```
///
/// Note however that a [`From`] implementation is not provided to convert from
/// an array `[u8; N]` by value, as this wrapper requires a lifetime to
/// associate the data with, even if it's just the local `'_` lifetime or the
/// global `'static` lifetime.
impl<'a> ByteSlice<'a> {
  /// Wrap a byte slice so it can be used by hyperscan.
  ///
  /// This method is [`const`](https://doc.rust-lang.org/std/keyword.const.html) so it can be used
  /// to define `const` values as well as
  /// [`static`](https://doc.rust-lang.org/std/keyword.static.html) initializers.
  pub const fn from_slice(data: &'a [u8]) -> Self { Self(data) }

  /// Extract the byte slice.
  ///
  /// A [slice](prim@slice) can be split into a pointer/length pair which is
  /// consumed by hyperscan's underlying C ABI.
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
/// [`str`](prim@str):
///
///```
/// use hyperscan::sources::ByteSlice;
///
/// let b1 = ByteSlice::from_str("asdf");
/// let b2: ByteSlice = "asdf".into();
/// assert_eq!(b1, b2);
/// assert_eq!(unsafe { b1.as_str() }, "asdf");
/// ```
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
  /// Wrap a UTF8-encoded byte slice so it can be used by hyperscan.
  ///
  /// As with [`Self::from_slice()`], this method is `const` and can produce
  /// `const` values or `static` initializers.
  pub const fn from_str(data: &'a str) -> Self { Self::from_slice(data.as_bytes()) }

  /// Extract the byte slice, and assert that it is correctly UTF8-encoded.
  ///
  /// # Safety
  /// This method avoids the overhead of repeatedly validating the underlying
  /// string data in the common case where all strings are UTF-8. Where this
  /// is not certain, [`Self::as_slice()`] can be provided to methods that check
  /// for UTF-8 validity:
  ///
  ///```
  /// use hyperscan::sources::ByteSlice;
  /// use std::str;
  ///
  /// // All-or-nothing UTF8 conversion with error:
  /// let b = ByteSlice::from_slice(b"asdf");
  /// let s = str::from_utf8(b.as_slice()).unwrap();
  /// assert_eq!(s, "asdf");
  ///
  /// // Error-handling UTF8 conversion which replaces invalid characters:
  /// let b = ByteSlice::from_slice(b"Hello \xF0\x90\x80World");
  /// let s = String::from_utf8_lossy(b.as_slice());
  /// assert_eq!("Hello �World", s);
  /// ```
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
  /// Return a subset of the input, or [`None`] if the result would be out of
  /// range:
  ///
  ///```
  /// use hyperscan::sources::ByteSlice;
  ///
  /// let b: ByteSlice = "asdf".into();
  /// let b2 = b.index_range(0..2).unwrap();
  /// assert_eq!(unsafe { b2.as_str() }, "as");
  /// assert!(b.index_range(0..5).is_none());
  /// ```
  ///
  /// This method is largely intended for internal use inside this library, but
  /// is exposed in the public API to make it clear how the match callback
  /// converts match offsets to substrings of the original input data.
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.as_slice().get(range).map(Self::from_slice)
  }
}

/// A [`slice`](prim@slice) of [`ByteSlice`].
///
/// This struct wraps non-contiguous slices of string data to pass to the
/// [`scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored) search
/// method, which produces match results of type
/// [`VectoredMatch`](crate::matchers::vectored_slice::VectoredMatch)
/// pointing to a subset of the original data.
///
/// This is currently implemented as
/// a [`#[repr(transparent)]`](https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent)
/// wrapper over `&'a [ByteSlice<'a>]`. The same lifetime `'a` is associated to
/// both the `ByteSlice<'a>` data entries themselves, as well as the location of
/// the slice which contains those `ByteSlice<'a>`s.
#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct VectoredByteSlices<'a>(&'a [ByteSlice<'a>]);

/// # Byte-Oriented Interface
/// Because hyperscan only partially supports vectored string inputs, this
/// library does not attempt to provide a UTF8-encoded [`str`](prim@str)
/// interface for vectored strings as with [`ByteSlice`].
impl<'a> VectoredByteSlices<'a> {
  pub const fn from_slices(data: &'a [ByteSlice<'a>]) -> Self { Self(data) }

  pub(crate) fn pointers_and_lengths(&self) -> (Vec<*const c_char>, Vec<c_uint>) {
    let lengths: Vec<c_uint> = self.0.iter().map(|col| col.native_len()).collect();
    let data_pointers: Vec<*const c_char> = self.0.iter().map(|col| col.as_ptr()).collect();
    (data_pointers, lengths)
  }

  pub(crate) const fn native_len(&self) -> c_uint { self.0.len() as c_uint }
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

/* FIXME: remove dynamic memory allocation! This can be handled! */
/// # Ownership and Indexing
/// Unlike with [`ByteSlice`], keeping track of a subset of vectored strings
/// requires some dynamic memory allocation, since a subset of vectored data may
/// start or stop in the middle of a particular slice. As a result,
/// [`Self::index_range()`] cannot return `Self` without allocating new memory
/// the way [`ByteSlice::index_range()`] can.
impl<'a> VectoredByteSlices<'a> {
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

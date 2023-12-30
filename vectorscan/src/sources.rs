/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Wrappers for types of string data which can be searched and indexed.
//!
//! These objects are used to provide string data for inputs to search functions
//! like [`scan_sync()`](crate::state::Scratch::scan_sync), and subsets of those
//! arguments are received as outputs by match callbacks to produce match info
//! such as [`Match`](crate::matchers::Match).

use std::{
  fmt,
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
/// Vectorscan can search over arbitrary byte patterns in any encoding, so
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
/// use vectorscan::sources::ByteSlice;
///
/// let b1 = ByteSlice::from_slice(b"asdf");
/// let b2: ByteSlice = b"asdf".into();
/// let b3: ByteSlice = [b'a', b's', b'd', b'f'].as_ref().into();
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
  /// Wrap a byte slice so it can be used by vectorscan.
  ///
  /// This method is [`const`](https://doc.rust-lang.org/std/keyword.const.html) so it can be used
  /// to define `const` values as well as
  /// [`static`](https://doc.rust-lang.org/std/keyword.static.html) initializers.
  pub const fn from_slice(data: &'a [u8]) -> Self { Self(data) }

  /// Extract the byte slice.
  ///
  /// A [slice](prim@slice) can be split into a pointer/length pair which is
  /// consumed by vectorscan's underlying C ABI.
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
/// When vectorscan is being used with UTF8-encoded inputs (e.g. with
/// [`Self::from_str()`]), it will produce UTF8 encoded match outputs, and
/// [`Self::as_str()`] can be invoked safely on match results.
///
/// A [`From`] implementation is also provided to convert from a native
/// [`str`](prim@str):
///
///```
/// use vectorscan::sources::ByteSlice;
///
/// let b1 = ByteSlice::from_str("asdf");
/// let b2: ByteSlice = "asdf".into();
/// assert_eq!(b1, b2);
/// assert_eq!(unsafe { b1.as_str() }, "asdf");
/// ```
///
/// ## The `UTF8` Flag
/// It is important to note that vectorscan itself does not assume any
/// particular string encoding, and the function of e.g.
/// [`Flags::UTF8`](crate::flags::Flags::UTF8) is to determine which bytes
/// should be included in the state machine, *not* the encoding of any
/// particular input. This means that the UTF8 flag may be disabled for UTF8
/// inputs to produce a much smaller state machine (as it is when using
/// [`Flags::default()`](crate::flags::Flags::default)). Note however that
/// enabling the UTF8 flag for non-UTF8 inputs produces undefined behavior.
impl<'a> ByteSlice<'a> {
  /// Wrap a UTF8-encoded byte slice so it can be used by vectorscan.
  ///
  /// As with [`Self::from_slice()`], this method is `const` and can produce
  /// `const` values or `static` initializers.
  pub const fn from_str(data: &'a str) -> Self { Self::from_slice(data.as_bytes()) }

  /// Extract the byte slice, and assert that it is correctly UTF8-encoded.
  ///
  /// # Safety
  /// This method passes the result of [`Self::as_slice()`] to
  /// [`str::from_utf8_unchecked()`] in order to avoid the overhead of
  /// repeatedly validating the underlying string data in the common case
  /// where all strings are UTF-8. Where this is not certain, the slice may be
  /// provided to methods such as [`str::from_utf8()`] or
  /// [`String::from_utf8_lossy()`] that check for UTF-8 validity:
  ///
  ///```
  /// use vectorscan::sources::ByteSlice;
  /// use std::{borrow::Cow, str};
  ///
  /// // All-or-nothing UTF8 conversion with error:
  /// let b = ByteSlice::from_slice(b"asdf");
  /// let s = str::from_utf8(b.as_slice()).unwrap();
  /// assert_eq!(s, "asdf");
  ///
  /// // Error-coercing UTF8 conversion which replaces invalid characters:
  /// let b = ByteSlice::from_slice(b"Hello \xF0\x90\x80World");
  /// let s: Cow<'_, str> = String::from_utf8_lossy(b.as_slice());
  /// assert_eq!(s, "Hello �World");
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
  /// use vectorscan::sources::ByteSlice;
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

#[cfg(feature = "vectored")]
#[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
pub mod vectored {
  use super::ByteSlice;

  use std::{
    cmp, mem, ops,
    os::raw::{c_char, c_uint},
    slice,
  };

  /// A [`slice`](prim@slice) of [`ByteSlice`].
  ///
  /// This struct wraps non-contiguous slices of string data to pass to the
  /// [`scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored) search
  /// method, which produces match results of type
  /// [`VectoredMatch`](crate::matchers::VectoredMatch)
  /// pointing to a subset of the original data.
  ///
  /// This is currently implemented as
  /// a [`#[repr(transparent)]`](https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent)
  /// wrapper over `&'slice [ByteSlice<'string>]`.
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct VectoredByteSlices<'string, 'slice>(&'slice [ByteSlice<'string>]);

  /// # Byte-Oriented Interface
  /// Because vectorscan only partially supports vectored string inputs, this
  /// library does not attempt to provide a UTF8-encoded [`str`](prim@str)
  /// interface for vectored strings as with [`ByteSlice`].
  ///
  /// However, [`From`] implementations are still provided to convert from
  /// references to [arrays](prim@array) and [slices](prim@slice):
  ///
  ///```
  /// use vectorscan::sources::vectored::VectoredByteSlices;
  ///
  /// let b1 = b"asdf";
  /// let b2 = b"bbbb";
  /// let bb = [b1.into(), b2.into()];
  /// let bs = VectoredByteSlices::from_slices(&bb);
  /// let bb2 = [b1.as_ref(), b2.as_ref()];
  /// let bs2: VectoredByteSlices = bb2.as_ref().into();
  /// assert_eq!(bs, bs2);
  /// ```
  impl<'string, 'slice> VectoredByteSlices<'string, 'slice> {
    /// Wrap a slice of byte slices so they can be scanned in vectored mode.
    ///
    /// Like [`ByteSlice::from_slice()`], this method is `const` so it can be
    /// used in `const` values and `static` initializers.
    pub const fn from_slices(data: &'slice [ByteSlice<'string>]) -> Self { Self(data) }

    pub fn length_sum(&self) -> usize { self.0.iter().map(|s| s.as_slice().len()).sum() }

    pub(crate) fn pointers_and_lengths(&self) -> (Vec<*const c_char>, Vec<c_uint>) {
      let lengths: Vec<c_uint> = self.0.iter().map(|col| col.native_len()).collect();
      let data_pointers: Vec<*const c_char> = self.0.iter().map(|col| col.as_ptr()).collect();
      (data_pointers, lengths)
    }

    pub(crate) const fn native_len(&self) -> c_uint { self.0.len() as c_uint }
  }

  impl<'string, 'slice> From<&'slice [ByteSlice<'string>]> for VectoredByteSlices<'string, 'slice> {
    fn from(x: &'slice [ByteSlice<'string>]) -> Self { Self::from_slices(x) }
  }

  impl<'string, 'slice, const N: usize> From<&'slice [ByteSlice<'string>; N]>
    for VectoredByteSlices<'string, 'slice>
  {
    fn from(x: &'slice [ByteSlice<'string>; N]) -> Self { Self::from_slices(x.as_ref()) }
  }

  impl<'string, 'slice> From<&'slice [&'string [u8]]> for VectoredByteSlices<'string, 'slice> {
    fn from(x: &'slice [&'string [u8]]) -> Self {
      let x: &'slice [ByteSlice<'string>] = unsafe { mem::transmute(x) };
      Self(x)
    }
  }

  impl<'string, 'slice, const N: usize> From<&'slice [&'string [u8]; N]>
    for VectoredByteSlices<'string, 'slice>
  {
    fn from(x: &'slice [&'string [u8]; N]) -> Self {
      let x: &'slice [ByteSlice<'string>; N] = unsafe { mem::transmute(x) };
      x.into()
    }
  }

  /// # Ownership and Indexing
  /// Keeping track of a subset of vectored strings
  /// requires some more work than for [`ByteSlice`], since a subset of vectored
  /// data may start or stop in the middle of a particular slice. As a result,
  /// [`Self::index_range()`] cannot simply return `Self` and return a reference
  /// to itself without allocating new memory the way
  /// [`ByteSlice::index_range()`] can.
  ///
  /// However, it *is* possible to avoid dynamic memory allocation when
  /// extracting subsets of vectored data; instead, [`Self::index_range()`]
  /// returns [`VectoredSubset`], which tracks offsets within the vectored
  /// string data without additional allocations.
  impl<'string, 'slice> VectoredByteSlices<'string, 'slice> {
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
    ) -> Option<VectoredSubset<'string, 'slice>> {
      let (start_col, start_ind) = start;
      let (end_col, end_ind) = end;
      assert!(end_col >= start_col);

      if start_col == end_col {
        assert!(end_ind >= start_ind);
        let col_substring = self.0[start_col].index_range(start_ind..end_ind)?;
        Some(VectoredSubset::from_single_slice(col_substring))
      } else {
        Some(VectoredSubset {
          start: Some(self.0[start_col].index_range(start_ind..)?),
          directly_referenced: &self.0[(start_col + 1)..end_col],
          end: Some(self.0[end_col].index_range(..end_ind)?),
        })
      }
    }

    /// Return a subset of the input, or [`None`] if the result would be out of
    /// range:
    ///
    ///```
    /// use vectorscan::sources::vectored::VectoredByteSlices;
    ///
    /// let b1 = "asdf";
    /// let b2 = "ok";
    /// let b3 = "bsdf";
    /// let bb = [b1.into(), b2.into(), b3.into()];
    /// let bs = VectoredByteSlices::from_slices(&bb);
    ///
    /// let sub = bs.index_range(2..8).unwrap();
    /// let collected: Vec<&str> = sub.iter_slices().map(|s| unsafe { s.as_str() }).collect();
    /// assert_eq!(&collected, &["df", "ok", "bs"]);
    /// ```
    ///
    /// This method is largely intended for internal use inside this library,
    /// but is exposed in the public API to make it clear how the match
    /// callback converts match offsets to substrings of the original input
    /// data.
    pub fn index_range(&self, range: ops::Range<usize>) -> Option<VectoredSubset<'string, 'slice>> {
      let ops::Range { start, end } = range;
      let (start_col, start_ind) = self.find_index_at(0, 0, start)?;
      let (end_col, end_ind) = self.find_index_at(start_col, start_ind, end - start)?;
      self.collect_slices_range((start_col, start_ind), (end_col, end_ind))
    }

    /// Iterate over all of the original vectored data.
    ///
    /// This is the corollary to [`VectoredSubset::iter_slices()`] and is mainly
    /// intended to aid in debugging.
    ///
    ///```
    /// use vectorscan::sources::vectored::VectoredByteSlices;
    ///
    /// let b1 = "asdf";
    /// let b2 = "ok";
    /// let b3 = "bbbb";
    /// let bb = [b1.into(), b2.into(), b3.into()];
    /// let bs = VectoredByteSlices::from_slices(&bb);
    ///
    /// let collected: Vec<&str> = bs.all_slices().map(|s| unsafe { s.as_str() }).collect();
    /// assert_eq!(&collected, &["asdf", "ok", "bbbb"]);
    /// ```
    pub fn all_slices(
      &self,
    ) -> impl Iterator<Item=ByteSlice<'string>>+ExactSizeIterator+DoubleEndedIterator+'_ {
      self.0.iter().cloned()
    }
  }

  /// A "ragged" subset of [`VectoredByteSlices`].
  ///
  /// This struct is able to reference a contiguous subset of the vectored
  /// string data contained in a [`VectoredByteSlices`], including any
  /// "ragged" start or end component which does not span the entirety of the
  /// corresponding slice from the input data. This allows the match callback
  /// provided to
  /// [`scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored) to
  /// receive [`VectoredMatch`](crate::matchers::VectoredMatch)
  /// instances that reference the input data without introducing
  /// any additional dynamic allocations.
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct VectoredSubset<'string, 'slice> {
    start: Option<ByteSlice<'string>>,
    directly_referenced: &'slice [ByteSlice<'string>],
    end: Option<ByteSlice<'string>>,
  }

  impl<'string, 'slice> VectoredSubset<'string, 'slice> {
    pub(crate) fn from_single_slice(data: ByteSlice<'string>) -> Self {
      Self {
        start: Some(data),
        directly_referenced: &[],
        end: None,
      }
    }

    /// Iterate over the referenced data.
    ///
    ///```
    /// use vectorscan::sources::vectored::VectoredByteSlices;
    ///
    /// let b1 = "asdf";
    /// let b2 = "ok";
    /// let b3 = "bsdf";
    /// let bb = [b1.into(), b2.into(), b3.into()];
    /// let bs = VectoredByteSlices::from_slices(&bb);
    ///
    /// let sub = bs.index_range(2..8).unwrap();
    /// let collected: Vec<&str> = sub.iter_slices().map(|s| unsafe { s.as_str() }).collect();
    /// assert_eq!(&collected, &["df", "ok", "bs"]);
    /// ```
    ///
    /// This iterator is the only interface exposed to access the data because
    /// "ragged" start and end components cannot be expressed as simple
    /// subslices of the vectored data in a [`VectoredByteSlices`], so the first
    /// and/or last iteration result must come from additional references to
    /// ragged substrings which are also stored in this struct.
    pub fn iter_slices(
      &self,
    ) -> impl Iterator<Item=ByteSlice<'string>>+ExactSizeIterator+DoubleEndedIterator+'_ {
      VectorIter::new(self)
    }
  }

  struct VectorIter<'string, 'slice> {
    done_start: Option<&'slice ByteSlice<'string>>,
    done_inner: slice::Iter<'slice, ByteSlice<'string>>,
    done_end: Option<&'slice ByteSlice<'string>>,
  }

  impl<'string, 'slice> VectorIter<'string, 'slice> {
    pub fn new(data: &'slice VectoredSubset<'string, 'slice>) -> Self {
      Self {
        done_start: data.start.as_ref(),
        done_inner: data.directly_referenced.iter(),
        done_end: data.end.as_ref(),
      }
    }

    fn remaining_len(&self) -> usize {
      let mut len: usize = 0;
      if self.done_start.is_some() {
        len += 1;
      }
      len += self.done_inner.as_slice().len();
      if self.done_end.is_some() {
        len += 1;
      }
      len
    }
  }

  impl<'string, 'slice> Iterator for VectorIter<'string, 'slice> {
    type Item = ByteSlice<'string>;

    fn next(&mut self) -> Option<Self::Item> {
      if let Some(start) = self.done_start.take() {
        return Some(*start);
      }

      if let Some(inner) = self.done_inner.next() {
        return Some(*inner);
      }

      if let Some(end) = self.done_end.take() {
        return Some(*end);
      }

      None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
      let rem = self.remaining_len();
      (rem, Some(rem))
    }
  }

  impl<'string, 'slice> ExactSizeIterator for VectorIter<'string, 'slice> {}

  impl<'string, 'slice> DoubleEndedIterator for VectorIter<'string, 'slice> {
    fn next_back(&mut self) -> Option<Self::Item> {
      if let Some(end) = self.done_end.take() {
        return Some(*end);
      }

      if let Some(inner) = self.done_inner.next_back() {
        return Some(*inner);
      }

      if let Some(start) = self.done_start.take() {
        return Some(*start);
      }

      None
    }
  }
}

#[cfg(feature = "stream")]
#[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
pub mod stream {
  use std::{ops, os::raw::c_ulonglong};

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Range {
    pub from: usize,
    pub to: usize,
  }

  static_assertions::assert_eq_size!(Range, ops::Range<usize>);
  static_assertions::assert_eq_size!(usize, c_ulonglong);
  static_assertions::assert_eq_size!((c_ulonglong, c_ulonglong), ops::Range<usize>);

  impl Range {
    pub const fn from_range(x: ops::Range<usize>) -> Self {
      let ops::Range { start, end } = x;
      Self {
        from: start,
        to: end,
      }
    }

    pub const fn into_range(self) -> ops::Range<usize> {
      let Self { from, to } = self;
      from..to
    }
  }

  impl From<ops::Range<usize>> for Range {
    fn from(x: ops::Range<usize>) -> Self { Self::from_range(x) }
  }

  impl From<Range> for ops::Range<usize> {
    fn from(x: Range) -> Self { x.into_range() }
  }
}

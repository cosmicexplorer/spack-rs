/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Wrappers for string data that interact with C++.
//!
//! [`StringView`] is widely interchangeable with [`str`](prim@str) throughout
//! this crate in order to operate on non-UTF-8 borrowed text, and is used to
//! implement the [`str`](prim@str) interface. [`StringWrapper`] on the other
//! hand is used to manage owned string data, and can be resized as well as
//! converted into a [`StringView`] or [`StringMut`] to avoid reallocating
//! memory while retaining a C++-compatible string.

use crate::re2_c;
#[cfg(doc)]
use crate::RE2;

use std::{cmp, fmt, hash, marker::PhantomData, mem, ops, os::raw::c_char, ptr, slice, str};

/// FFI-compatible reference to a read-only slice of bytes.
///
///```
/// use re2::string::StringView;
///
/// let s: StringView = "asdf".into();
/// assert_eq!(s, StringView::from_str("asdf"));
/// assert_eq!(unsafe { s.as_str() }, "asdf");
/// assert_eq!(s, StringView::from_slice(b"asdf"));
/// assert_eq!(s.as_slice(), b"asdf");
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct StringView<'a> {
  inner: re2_c::StringView,
  _ph: PhantomData<&'a u8>,
}

impl<'a> StringView<'a> {
  /// Apply an indexing operation to extract a subset of this byte slice.
  ///
  ///```
  /// use re2::string::StringView;
  ///
  /// let mut s = StringView::from_str("asdf");
  /// s = s.index_range(0..2).unwrap();
  /// assert_eq!(s.as_slice(), b"as");
  /// ```
  pub fn index_range(&self, range: impl slice::SliceIndex<[u8], Output=[u8]>) -> Option<Self> {
    self.as_slice().get(range).map(Self::from_slice)
  }

  /// Produce an empty string.
  ///
  ///```
  /// use re2::string::StringView;
  ///
  /// assert_eq!(unsafe { StringView::empty().as_str() }, "");
  /// ```
  pub const fn empty() -> Self {
    let inner = re2_c::StringView {
      data_: ptr::null(),
      len_: 0,
    };
    Self::from_native(inner)
  }

  pub(crate) const fn from_native(inner: re2_c::StringView) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  pub(crate) const fn into_native(self) -> re2_c::StringView { self.inner }

  /// Extract an FFI-compatible representation of a byte slice.
  pub const fn from_slice(b: &'a [u8]) -> Self {
    let inner = re2_c::StringView {
      data_: b.as_ptr() as *const c_char,
      len_: b.len(),
    };
    Self::from_native(inner)
  }

  /// Extract an FFI-compatible representation of a string's backing byte slice.
  pub const fn from_str(s: &'a str) -> Self { Self::from_slice(s.as_bytes()) }

  const unsafe fn data_pointer(&self) -> *const u8 { mem::transmute(self.inner.data_) }

  /// Whether the slice has any data.
  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  /// The number of bytes in the slice.
  pub const fn len(&self) -> usize { self.inner.len_ }

  /// Produce a Rust-compatible view of this byte slice.
  pub const fn as_slice(&self) -> &'a [u8] {
    unsafe { slice::from_raw_parts(self.data_pointer(), self.len()) }
  }

  /// Produce a Rust string view of this byte slice.
  pub const unsafe fn as_str(&self) -> &'a str { str::from_utf8_unchecked(self.as_slice()) }

  /* Used in "consume" methods which may update a string view to a substring
   * upon match. */
  pub(crate) fn as_mut_native(&mut self) -> &mut re2_c::StringView { &mut self.inner }
}

impl<'a> From<&'a [u8]> for StringView<'a> {
  fn from(x: &'a [u8]) -> Self { Self::from_slice(x) }
}

impl<'a, const N: usize> From<&'a [u8; N]> for StringView<'a> {
  fn from(x: &'a [u8; N]) -> Self { Self::from_slice(x.as_ref()) }
}

impl<'a> From<&'a str> for StringView<'a> {
  fn from(x: &'a str) -> Self { Self::from_str(x) }
}

impl<'a> Default for StringView<'a> {
  fn default() -> Self { Self::empty() }
}

impl<'a> fmt::Debug for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let s = self.as_slice();
    match str::from_utf8(s) {
      Ok(s) => write!(f, "{:?}", s),
      Err(_) => write!(f, "{:?}", s),
    }
  }
}

impl<'a> fmt::Display for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let s = self.as_slice();
    match str::from_utf8(s) {
      Ok(s) => write!(f, "{}", s),
      Err(_) => write!(f, "{:?}", s),
    }
  }
}

impl<'a> cmp::PartialEq for StringView<'a> {
  fn eq(&self, other: &Self) -> bool { self.as_slice().eq(other.as_slice()) }
}

impl<'a> cmp::Eq for StringView<'a> {}

impl<'a> cmp::PartialOrd for StringView<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl<'a> cmp::Ord for StringView<'a> {
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_slice().cmp(other.as_slice()) }
}

impl<'a> hash::Hash for StringView<'a> {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.as_slice().hash(state);
  }
}

/// FFI-compatible reference to a mutable slice of bytes.
///
///```
/// use re2::string::StringMut;
///
/// let mut s = "asdf".to_string();
/// let s1 = StringMut::from_mut_str(&mut s);
/// assert_eq!(unsafe { s1.as_mut_str() }, "asdf");
/// s1.as_mut_slice()[2] = b'e';
/// assert_eq!(s1.as_mut_slice(), b"asef");
///
/// let mut s2 = *b"asdf";
/// let s3 = StringMut::from_mut_slice(&mut s2);
/// s3.as_mut_slice()[2] = b'e';
/// assert_eq!(s3, s1);
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct StringMut<'a> {
  inner: re2_c::StringMut,
  _ph: PhantomData<&'a mut u8>,
}

impl<'a> StringMut<'a> {
  /// Produce an empty string.
  ///
  ///```
  /// use re2::string::StringMut;
  ///
  /// assert_eq!(unsafe { StringMut::empty().as_mut_str() }, "");
  /// ```
  pub fn empty() -> Self {
    let inner = re2_c::StringMut {
      data_: ptr::null_mut(),
      len_: 0,
    };
    Self::from_native(inner)
  }

  /* NB: This can't be const because it references &mut data! */
  pub(crate) fn from_native(inner: re2_c::StringMut) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  /* NB: This can't be const because it references &mut data! */
  /// Extract an FFI-compatible representation of a mutable byte slice.
  pub fn from_mut_slice(b: &'a mut [u8]) -> Self {
    let inner = re2_c::StringMut {
      data_: b.as_mut_ptr() as *mut c_char,
      len_: b.len(),
    };
    Self::from_native(inner)
  }

  /* NB: not const bc .as_bytes_mut() isn't const!! */
  /// Extract an FFI-compatible representation of a mutable string's backing
  /// byte slice.
  pub fn from_mut_str(s: &'a mut str) -> Self { Self::from_mut_slice(unsafe { s.as_bytes_mut() }) }

  const unsafe fn mut_data_pointer(&self) -> *mut u8 { mem::transmute(self.inner.data_) }

  /// Whether the slice has any data.
  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  /// The number of bytes in the slice.
  pub const fn len(&self) -> usize { self.inner.len_ }

  /// Produce a Rust-compatible view of this mutable byte slice.
  pub fn as_mut_slice(&self) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(self.mut_data_pointer(), self.len()) }
  }

  /// Produce a Rust string view of this mutable byte slice.
  pub unsafe fn as_mut_str(&self) -> &'a mut str {
    str::from_utf8_unchecked_mut(self.as_mut_slice())
  }
}

impl<'a> From<&'a mut [u8]> for StringMut<'a> {
  fn from(x: &'a mut [u8]) -> Self { Self::from_mut_slice(x) }
}

impl<'a, const N: usize> From<&'a mut [u8; N]> for StringMut<'a> {
  fn from(x: &'a mut [u8; N]) -> Self { Self::from_mut_slice(x.as_mut()) }
}

impl<'a> From<&'a mut str> for StringMut<'a> {
  fn from(x: &'a mut str) -> Self { Self::from_mut_str(x) }
}

impl<'a> Default for StringMut<'a> {
  fn default() -> Self { Self::empty() }
}

impl<'a> fmt::Debug for StringMut<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let s = self.as_mut_slice();
    match str::from_utf8(s) {
      Ok(s) => write!(f, "{:?}", s),
      Err(_) => write!(f, "{:?}", s),
    }
  }
}

impl<'a> fmt::Display for StringMut<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let s = self.as_mut_slice();
    match str::from_utf8(s) {
      Ok(s) => write!(f, "{}", s),
      Err(_) => write!(f, "{:?}", s),
    }
  }
}

impl<'a> cmp::PartialEq for StringMut<'a> {
  fn eq(&self, other: &Self) -> bool { self.as_mut_slice().eq(&other.as_mut_slice()) }
}

impl<'a> cmp::Eq for StringMut<'a> {}

impl<'a> cmp::PartialOrd for StringMut<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl<'a> cmp::Ord for StringMut<'a> {
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_mut_slice().cmp(&other.as_mut_slice()) }
}

impl<'a> hash::Hash for StringMut<'a> {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.as_mut_slice().hash(state);
  }
}

/// Handle to a heap-allocated C++ `std::string`.
///
/// This is used as an output for some string search methods such as
/// [`RE2::extract()`] which need to allocate memory dynamically. The same
/// instance can be provided to multiple calls in order to avoid allocating a
/// new string upon each call, and [`Self::as_mut_view()`] and
/// [`Self::resize()`] can be used to modify the contents in between calls.
///
/// This object "owns" its string data, and upon destruction, this object will
/// deallocate the underlying `std::string` data as well. Use
/// [`Self::as_view()`] to extract a view of the underlying data in order to
/// copy it elsewhere.
#[derive(Debug)]
#[repr(transparent)]
pub struct StringWrapper(re2_c::StringWrapper);

impl StringWrapper {
  /// Generate an instance without allocating any memory dynamically.
  ///
  ///```
  /// let s = re2::string::StringWrapper::blank();
  /// assert_eq!(unsafe { s.as_view().as_str() }, "");
  /// ```
  pub const fn blank() -> Self {
    Self(re2_c::StringWrapper {
      inner_: ptr::null_mut(),
    })
  }

  /// Generate an instance which copies the bytes from the argument `s`.
  ///
  ///```
  /// let s = re2::string::StringWrapper::from_view("asdf".into());
  /// assert_eq!(unsafe { s.as_view().as_str() }, "asdf");
  /// ```
  pub fn from_view(s: StringView) -> Self {
    Self(unsafe { re2_c::StringWrapper::new(s.into_native()) })
  }

  pub(crate) fn as_mut_native(&mut self) -> &mut re2_c::StringWrapper { &mut self.0 }

  /// Generate a read-only view of the dynamically allocated memory.
  ///
  ///```
  /// let s = re2::string::StringWrapper::from_view("asdf".into());
  /// assert_eq!(unsafe { s.as_view().as_str() }, "asdf");
  /// ```
  pub fn as_view(&self) -> StringView { unsafe { StringView::from_native(self.0.as_view()) } }

  /// Generate a mutable view of the dynamically allocated memory.
  ///
  ///```
  /// let mut s = re2::string::StringWrapper::from_view("asdf".into());
  /// s.as_mut_view().as_mut_slice()[2] = b'e';
  /// assert_eq!(unsafe { s.as_view().as_str() }, "asef");
  /// ```
  pub fn as_mut_view(&mut self) -> StringMut<'_> {
    unsafe { StringMut::from_native(self.0.as_mut_view()) }
  }

  /// Resize the underlying `std::string` storage.
  ///
  /// If the new length is larger than the old, this method will pad the result
  /// with null bytes.
  ///
  ///```
  /// let mut s = re2::string::StringWrapper::from_view("asdf".into());
  /// assert_eq!(unsafe { s.as_view().as_str() }, "asdf");
  /// s.resize(2);
  /// assert_eq!(unsafe { s.as_view().as_str() }, "as");
  /// s.resize(6);
  /// assert_eq!(unsafe { s.as_view().as_str() }, "as\0\0\0\0");
  /// s.resize(0);
  /// assert_eq!(unsafe { s.as_view().as_str() }, "");
  /// ```
  pub fn resize(&mut self, len: usize) {
    unsafe {
      self.0.resize(len);
    }
  }

  /// Deallocate the underlying string storage.
  ///
  /// This method is idempotent and can be called multiple times in a row.
  ///
  ///```
  /// let mut s = re2::string::StringWrapper::from_view("asdf".into());
  /// assert_eq!(unsafe { s.as_view().as_str() }, "asdf");
  /// s.clear();
  /// assert_eq!(unsafe { s.as_view().as_str() }, "");
  /// ```
  pub fn clear(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

impl ops::Drop for StringWrapper {
  fn drop(&mut self) { self.clear(); }
}

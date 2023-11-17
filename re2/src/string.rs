/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::re2_c;

use std::{cmp, fmt, hash, marker::PhantomData, mem, ops, os::raw::c_char, ptr, slice, str};

///```
/// use re2::StringView;
///
/// let s = StringView::from_str("asdf");
/// assert_eq!(s.as_str(), "asdf");
/// assert_eq!(StringView::empty().as_str(), "");
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct StringView<'a> {
  inner: re2_c::StringView,
  _ph: PhantomData<&'a u8>,
}

impl<'a> StringView<'a> {
  #[inline]
  pub const fn empty() -> Self {
    let inner = re2_c::StringView {
      data_: ptr::null(),
      len_: 0,
    };
    unsafe { Self::from_native(inner) }
  }

  #[inline]
  pub(crate) const unsafe fn from_native(inner: re2_c::StringView) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  #[inline]
  pub(crate) const fn into_native(self) -> re2_c::StringView { self.inner }

  #[inline]
  pub const fn from_slice(b: &'a [u8]) -> Self {
    let inner = re2_c::StringView {
      data_: b.as_ptr() as *const c_char,
      len_: b.len(),
    };
    unsafe { Self::from_native(inner) }
  }

  #[inline]
  pub const fn from_str(s: &'a str) -> Self { Self::from_slice(s.as_bytes()) }

  #[inline]
  const unsafe fn data_pointer(&self) -> *const u8 { mem::transmute(self.inner.data_) }

  #[inline]
  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  #[inline]
  pub const fn len(&self) -> usize { self.inner.len_ }

  #[inline]
  pub const fn as_slice(&self) -> &'a [u8] {
    unsafe { slice::from_raw_parts(self.data_pointer(), self.len()) }
  }

  #[inline]
  pub const fn as_str(&self) -> &'a str { unsafe { str::from_utf8_unchecked(self.as_slice()) } }

  /* Used in "consume" methods which may update a string view to a substring upon match. */
  #[inline]
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
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{:?}", self.as_str()) }
}

impl<'a> fmt::Display for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
}

impl<'a> cmp::PartialEq for StringView<'a> {
  fn eq(&self, other: &Self) -> bool { self.as_slice().eq(other.as_slice()) }
}

impl<'a> cmp::Eq for StringView<'a> {}

impl<'a> cmp::PartialOrd for StringView<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    self.as_slice().partial_cmp(other.as_slice())
  }
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

///```
/// use re2::StringMut;
///
/// let mut s = "asdf".to_string();
/// let s1 = StringMut::from_mut_str(&mut s);
/// assert_eq!(s1.as_mut_str(), "asdf");
/// s1.as_mut_slice()[2] = b'e';
/// assert_eq!(s1.as_mut_str(), "asef");
/// assert_eq!(StringMut::empty().as_mut_str(), "");
///
/// let mut s = *b"asdf";
/// let s1 = StringMut::from_mut_slice(&mut s);
/// assert_eq!(s1.as_mut_str(), "asdf");
/// s1.as_mut_slice()[2] = b'e';
/// assert_eq!(s1.as_mut_str(), "asef");
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct StringMut<'a> {
  inner: re2_c::StringMut,
  _ph: PhantomData<&'a mut u8>,
}

impl<'a> StringMut<'a> {
  #[inline]
  pub const fn empty() -> Self {
    let inner = re2_c::StringMut {
      data_: ptr::null_mut(),
      len_: 0,
    };
    unsafe { Self::from_native(inner) }
  }

  #[inline]
  pub(crate) const unsafe fn from_native(inner: re2_c::StringMut) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  #[inline]
  pub const fn from_mut_slice(b: &'a mut [u8]) -> Self {
    let inner = re2_c::StringMut {
      data_: b.as_mut_ptr() as *mut c_char,
      len_: b.len(),
    };
    unsafe { Self::from_native(inner) }
  }

  /* NB: not const bc .as_bytes_mut() isn't const!! */
  #[inline]
  pub fn from_mut_str(s: &'a mut str) -> Self { Self::from_mut_slice(unsafe { s.as_bytes_mut() }) }

  #[inline]
  const unsafe fn mut_data_pointer(&self) -> *mut u8 { mem::transmute(self.inner.data_) }

  #[inline]
  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  #[inline]
  pub const fn len(&self) -> usize { self.inner.len_ }

  #[inline]
  pub const fn as_mut_slice(&self) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(self.mut_data_pointer(), self.len()) }
  }

  #[inline]
  pub const fn as_mut_str(&self) -> &'a mut str {
    unsafe { str::from_utf8_unchecked_mut(self.as_mut_slice()) }
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
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{:?}", self.as_mut_str()) }
}

impl<'a> fmt::Display for StringMut<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_mut_str()) }
}

impl<'a> cmp::PartialEq for StringMut<'a> {
  fn eq(&self, other: &Self) -> bool { self.as_mut_slice().eq(&other.as_mut_slice()) }
}

impl<'a> cmp::Eq for StringMut<'a> {}

impl<'a> cmp::PartialOrd for StringMut<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    self.as_mut_slice().partial_cmp(&other.as_mut_slice())
  }
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

#[derive(Debug)]
#[repr(transparent)]
pub struct StringWrapper(re2_c::StringWrapper);

impl StringWrapper {
  ///```
  /// let s = re2::StringWrapper::blank();
  /// assert_eq!(s.as_view().as_str(), "");
  /// ```
  #[inline]
  pub const fn blank() -> Self {
    Self(re2_c::StringWrapper {
      inner_: ptr::null_mut(),
    })
  }

  #[inline]
  pub fn from_view(s: StringView<'_>) -> Self {
    Self(unsafe { re2_c::StringWrapper::new(s.into_native()) })
  }

  #[inline]
  pub(crate) fn as_mut_native(&mut self) -> &mut re2_c::StringWrapper { &mut self.0 }

  ///```
  /// let s = re2::StringWrapper::from_view("asdf".into());
  /// assert_eq!(s.as_view().as_str(), "asdf");
  /// ```
  #[inline]
  pub fn as_view(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.as_view()) } }

  ///```
  /// let mut s = re2::StringWrapper::from_view("asdf".into());
  /// s.as_mut_view().as_mut_slice()[2] = b'e';
  /// assert_eq!(s.as_view().as_str(), "asef");
  /// ```
  #[inline]
  pub fn as_mut_view(&mut self) -> StringMut<'_> {
    unsafe { StringMut::from_native(self.0.as_mut_view()) }
  }

  ///```
  /// let mut s = re2::StringWrapper::from_view("asdf".into());
  /// assert_eq!(s.as_view().as_str(), "asdf");
  /// s.resize(2);
  /// assert_eq!(s.as_view().as_str(), "as");
  /// s.resize(6);
  /// assert_eq!(s.as_view().as_str(), "as\0\0\0\0");
  /// s.resize(0);
  /// assert_eq!(s.as_view().as_str(), "");
  /// ```
  #[inline]
  pub fn resize(&mut self, len: usize) {
    unsafe {
      self.0.resize(len);
    }
  }

  ///```
  /// let mut s = re2::StringWrapper::from_view("asdf".into());
  /// assert_eq!(s.as_view().as_str(), "asdf");
  /// s.clear();
  /// assert_eq!(s.as_view().as_str(), "");
  /// ```
  #[inline]
  pub fn clear(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

impl ops::Drop for StringWrapper {
  fn drop(&mut self) { self.clear(); }
}

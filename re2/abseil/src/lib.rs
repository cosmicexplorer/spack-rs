/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

#[allow(unused)]
mod bindings;

use bindings::root::absl::lts_20230125 as absl;

use std::{cmp, fmt, hash, marker::PhantomData, mem, ops, slice, str};

///```
/// use abseil::StringView;
///
/// let s = StringView::from_str("a");
///
/// assert_eq!(s, StringView::from_str("a"));
/// assert_eq!(s.as_str(), "a");
/// assert_eq!(&format!("{}", &s), "a");
/// assert_eq!(&format!("{:?}", &s), "\"a\"");
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct StringView<'a> {
  pub inner: absl::string_view,
  _ph: PhantomData<&'a u8>,
}

impl<'a> StringView<'a> {
  #[inline]
  pub const unsafe fn from_native(inner: absl::string_view) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  #[inline]
  pub const fn from_str(s: &'a str) -> Self {
    let b = s.as_bytes();
    let v: absl::string_view = [unsafe { mem::transmute(b.as_ptr()) }, b.len() as u64];
    Self {
      inner: v,
      _ph: PhantomData,
    }
  }

  #[inline]
  pub const fn as_str(&self) -> &'a str {
    let Self {
      inner: [p, length], ..
    } = self;
    let span: &'a [u8] = unsafe { slice::from_raw_parts(mem::transmute(*p), *length as usize) };
    unsafe { str::from_utf8_unchecked(span) }
  }
}

impl<'a> AsRef<str> for StringView<'a> {
  fn as_ref(&self) -> &str { self.as_str() }
}

impl<'a> ops::Deref for StringView<'a> {
  type Target = str;

  fn deref(&self) -> &str { self.as_str() }
}

impl<'a> fmt::Display for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
}

impl<'a> fmt::Debug for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\"{}\"", self.as_str()) }
}

impl<'a> cmp::PartialEq for StringView<'a> {
  fn eq(&self, other: &Self) -> bool { self.as_str().eq(other.as_str()) }
}

impl<'a> cmp::Eq for StringView<'a> {}

impl<'a> cmp::PartialOrd for StringView<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    self.as_str().partial_cmp(other.as_str())
  }
}

impl<'a> cmp::Ord for StringView<'a> {
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_str().cmp(other.as_str()) }
}

impl<'a> hash::Hash for StringView<'a> {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.as_str().hash(state);
  }
}

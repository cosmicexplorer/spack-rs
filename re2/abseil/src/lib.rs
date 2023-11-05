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

use std::{cmp, fmt, hash, mem, slice, str};

///```
/// use abseil::StringView;
///
/// let s = StringView::from_str("a");
///
/// assert_eq!(s.as_str(), "a");
/// assert_eq!(&format!("{}", &s), "a");
/// assert_eq!(&format!("{:?}", &s), "\"a\"");
/// ```
#[repr(transparent)]
pub struct StringView(pub absl::string_view);

impl StringView {
  #[inline]
  pub const fn from_str(s: &str) -> Self {
    Self(absl::string_view {
      ptr_: unsafe { mem::transmute(s.as_bytes().as_ptr()) },
      length_: s.len(),
    })
  }

  #[inline]
  pub const fn as_str(&self) -> &str {
    let Self(absl::string_view { ptr_, length_ }) = self;
    let span: &[u8] = unsafe { slice::from_raw_parts(mem::transmute(*ptr_), *length_) };
    unsafe { str::from_utf8_unchecked(span) }
  }
}

impl fmt::Display for StringView {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
}

impl fmt::Debug for StringView {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\"{}\"", self.as_str()) }
}

impl cmp::PartialEq for StringView {
  fn eq(&self, other: &Self) -> bool { self.as_str().eq(other.as_str()) }
}

impl cmp::Eq for StringView {}

impl cmp::PartialOrd for StringView {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    self.as_str().partial_cmp(other.as_str())
  }
}

impl cmp::Ord for StringView {
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_str().cmp(other.as_str()) }
}

impl hash::Hash for StringView {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.as_str().hash(state);
  }
}

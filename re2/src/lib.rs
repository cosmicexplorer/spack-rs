/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

#[allow(unused, improper_ctypes)]
mod bindings;

use bindings::root::re2;

use abseil::StringView;

use std::{mem, ptr};

///```
/// use abseil::StringView;
/// use re2::RE2;
///
/// let p = StringView::from_str("he");
/// let r = RE2::new(&p);
/// assert!(r.full_match(&StringView::from_str("he")));
/// assert!(r.partial_match(&StringView::from_str("hello")));
/// assert!(r.partial_match(&StringView::from_str("the")));
/// ```
pub struct RE2(pub re2::RE2);

impl RE2 {
  pub fn new(pattern: &StringView) -> Self {
    /* NB: mem::transmute is currently needed (but always safe) because we
     * duplicate any native bindings across each crate. */
    Self(unsafe { re2::RE2::new2(mem::transmute(pattern.0)) })
  }

  #[inline]
  pub fn full_match(&self, text: &StringView) -> bool {
    unsafe { re2::RE2_FullMatchN(mem::transmute(text.0), &self.0, ptr::null(), 0) }
  }

  #[inline]
  pub fn partial_match(&self, text: &StringView) -> bool {
    unsafe { re2::RE2_PartialMatchN(mem::transmute(text.0), &self.0, ptr::null(), 0) }
  }
}

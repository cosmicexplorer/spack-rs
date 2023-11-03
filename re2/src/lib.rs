/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Turn all warnings into errors!
#![allow(warnings)]
// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Enable all clippy lints except for many of the pedantic ones. It's a shame this needs to be
 * copied and pasted across crates, but there doesn't appear to be a way to include inner
 * attributes from a common source. */
#![deny(
  clippy::all,
  clippy::default_trait_access,
  clippy::expl_impl_clone_on_copy,
  clippy::if_not_else,
  clippy::needless_continue,
  clippy::unseparated_literal_suffix,
  clippy::used_underscore_binding
)]
/* We use inner modules in several places in this crate for ergonomics. */
#![allow(clippy::module_inception)]
/* It is often more clear to show that nothing is being moved. */
#![allow(clippy::match_ref_pats)]
/* Subjective style. */
#![allow(
  clippy::len_without_is_empty,
  clippy::redundant_field_names,
  clippy::too_many_arguments,
  clippy::single_component_path_imports
)]
/* Default isn't as big a deal as people seem to think it is. */
#![allow(clippy::new_without_default, clippy::new_ret_no_self)]
/* Arc<Mutex> can be more clear than needing to grok Orderings: */
#![allow(clippy::mutex_atomic)]

mod bindings;

use bindings::root::re2;

use std::{ffi::CStr, fmt, mem, ops, ptr, slice, str};

///```
/// use re2::StringPiece;
///
/// let s = StringPiece::from_str("a");
///
/// assert_eq!(s.as_str(), "a");
/// assert_eq!(&format!("{}", &s), "a");
/// assert_eq!(&format!("{:?}", &s), "\"a\"");
/// ```
pub struct StringPiece(pub(crate) re2::StringPiece);

impl StringPiece {
  #[inline]
  pub const fn from_str(s: &str) -> Self {
    Self(re2::StringPiece {
      data_: unsafe { mem::transmute(s.as_bytes().as_ptr()) },
      size_: s.len(),
    })
  }

  #[inline]
  pub const fn as_str(&self) -> &str {
    let Self(re2::StringPiece { data_, size_ }) = self;
    let span: &[u8] = unsafe { slice::from_raw_parts(mem::transmute(*data_), *size_) };
    unsafe { str::from_utf8_unchecked(span) }
  }
}

impl fmt::Display for StringPiece {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
}

impl fmt::Debug for StringPiece {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\"{}\"", self.as_str()) }
}

///```
/// use re2::*;
///
/// let p = StringPiece::from_str("he");
/// let r = RE2::new(&p);
/// assert!(r.full_match(&StringPiece::from_str("he")));
/// assert!(r.partial_match(&StringPiece::from_str("hello")));
/// assert!(r.partial_match(&StringPiece::from_str("the")));
///```
pub struct RE2(pub(crate) re2::RE2);

impl RE2 {
  pub fn new(pattern: &StringPiece) -> Self { Self(unsafe { re2::RE2::new2(&pattern.0) }) }

  #[inline]
  pub fn full_match(&self, text: &StringPiece) -> bool {
    unsafe { re2::RE2_FullMatchN(&text.0, &self.0, ptr::null(), 0) }
  }

  #[inline]
  pub fn partial_match(&self, text: &StringPiece) -> bool {
    unsafe { re2::RE2_PartialMatchN(&text.0, &self.0, ptr::null(), 0) }
  }
}

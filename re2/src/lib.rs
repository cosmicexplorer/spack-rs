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

pub mod error;
use error::{CompileError, RE2ErrorCode};

pub(crate) use bindings::root::re2;

use abseil::StringView;

use std::{ffi::CStr, mem, ops, os::raw::c_char, ptr};

#[derive(
  Default,
  Debug,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::IntoPrimitive,
  num_enum::TryFromPrimitive,
)]
#[repr(u32)]
pub enum CannedOptions {
  #[default]
  DefaultOptions = re2::RE2_CannedOptions_DefaultOptions,
  Latin1 = re2::RE2_CannedOptions_Latin1,
  POSIX = re2::RE2_CannedOptions_POSIX,
  Quiet = re2::RE2_CannedOptions_Quiet,
}

impl CannedOptions {
  #[inline]
  pub fn into_native(self) -> re2::RE2_CannedOptions { self.into() }
}

#[derive(
  Default,
  Debug,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::IntoPrimitive,
  num_enum::TryFromPrimitive,
)]
#[repr(u32)]
pub enum Encoding {
  #[default]
  Utf8 = re2::RE2_Options_Encoding_EncodingUTF8,
  Latin1 = re2::RE2_Options_Encoding_EncodingLatin1,
}

impl Encoding {
  #[inline]
  pub fn into_native(self) -> re2::RE2_Options_Encoding { self.into() }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Options {
  pub max_mem: u32,
  pub encoding: Encoding,
  pub posix_syntax: bool,
  pub longest_match: bool,
  pub log_errors: bool,
  pub literal: bool,
  pub never_nl: bool,
  pub dot_nl: bool,
  pub never_capture: bool,
  pub case_sensitive: bool,
  pub perl_classes: bool,
  pub word_boundary: bool,
  pub one_line: bool,
}

impl Options {
  #[inline]
  pub fn into_native(self) -> re2::RE2_Options {
    let Self {
      max_mem,
      encoding,
      posix_syntax,
      longest_match,
      log_errors,
      literal,
      never_nl,
      dot_nl,
      never_capture,
      case_sensitive,
      perl_classes,
      word_boundary,
      one_line,
    } = self;
    re2::RE2_Options {
      max_mem_: max_mem as i64,
      encoding_: encoding.into_native(),
      posix_syntax_: posix_syntax,
      longest_match_: longest_match,
      log_errors_: log_errors,
      literal_: literal,
      never_nl_: never_nl,
      dot_nl_: dot_nl,
      never_capture_: never_capture,
      case_sensitive_: case_sensitive,
      perl_classes_: perl_classes,
      word_boundary_: word_boundary,
      one_line_: one_line,
    }
  }
}

impl From<re2::RE2_Options> for Options {
  #[inline]
  fn from(x: re2::RE2_Options) -> Self {
    let re2::RE2_Options {
      max_mem_,
      encoding_,
      posix_syntax_,
      longest_match_,
      log_errors_,
      literal_,
      never_nl_,
      dot_nl_,
      never_capture_,
      case_sensitive_,
      perl_classes_,
      word_boundary_,
      one_line_,
    } = x;
    Self {
      max_mem: max_mem_ as u32,
      encoding: encoding_.try_into().unwrap(),
      posix_syntax: posix_syntax_,
      longest_match: longest_match_,
      log_errors: log_errors_,
      literal: literal_,
      never_nl: never_nl_,
      dot_nl: dot_nl_,
      never_capture: never_capture_,
      case_sensitive: case_sensitive_,
      perl_classes: perl_classes_,
      word_boundary: word_boundary_,
      one_line: one_line_,
    }
  }
}

impl From<CannedOptions> for Options {
  fn from(x: CannedOptions) -> Self { unsafe { re2::RE2_Options::new(x.into_native()) }.into() }
}

impl Default for Options {
  fn default() -> Self {
    Self {
      max_mem: 8 << 20,
      encoding: Encoding::Utf8,
      posix_syntax: false,
      longest_match: false,
      log_errors: true,
      literal: false,
      never_nl: false,
      dot_nl: false,
      never_capture: false,
      case_sensitive: true,
      perl_classes: false,
      word_boundary: false,
      one_line: false,
    }
  }
}

///```
/// # fn main() -> Result<(), re2::error::CompileError> {
/// use re2::{RE2, error::*};
///
/// let r = RE2::new(".he")?;
/// assert!(r.full_match("the"));
/// assert!(!r.partial_match("hello"));
/// assert!(r.partial_match("othello"));
/// assert!(r.partial_match("the"));
///
/// assert_eq!(
///   CompileError {
///     message: Some("missing ): as(df".to_string()),
///     arg: Some("as(df".to_string()),
///     code: RE2ErrorCode::MissingParen,
///   },
///   RE2::new("as(df").err().unwrap(),
/// );
/// # Ok(())
/// # }
/// ```
#[repr(transparent)]
pub struct RE2(pub re2::RE2);

impl RE2 {
  fn parse_c_str(p: *const c_char) -> Option<String> {
    if p.is_null() {
      return None;
    }
    let c_str = unsafe { CStr::from_ptr(p) };
    Some(c_str.to_string_lossy().to_string())
  }

  fn check_error_state(&self) -> Result<(), CompileError> {
    RE2ErrorCode::from_native(self.0.error_code_()).map_err(|code| CompileError {
      message: Self::parse_c_str(unsafe { self.0.error_c() }),
      arg: Self::parse_c_str(unsafe { self.0.error_arg_c() }),
      code,
    })
  }

  pub fn new(pattern: impl AsRef<str>) -> Result<Self, CompileError> {
    let pattern = StringView::from_str(pattern.as_ref());
    /* NB: mem::transmute is currently needed (but always safe) because we
     * duplicate any native bindings across each crate. */
    let ret = Self(unsafe { re2::RE2::new2(mem::transmute(pattern.0)) });
    ret.check_error_state()?;
    Ok(ret)
  }

  pub fn new_with_options(
    pattern: impl AsRef<str>,
    options: Options,
  ) -> Result<Self, CompileError> {
    let pattern = StringView::from_str(pattern.as_ref());
    let ret = Self(unsafe { re2::RE2::new3(mem::transmute(pattern.0), &options.into_native()) });
    ret.check_error_state()?;
    Ok(ret)
  }

  #[inline]
  pub fn full_match(&self, text: impl AsRef<str>) -> bool {
    let text = StringView::from_str(text.as_ref());
    unsafe { re2::RE2_FullMatchN(mem::transmute(text.0), &self.0, ptr::null(), 0) }
  }

  #[inline]
  pub fn partial_match(&self, text: impl AsRef<str>) -> bool {
    let text = StringView::from_str(text.as_ref());
    unsafe { re2::RE2_PartialMatchN(mem::transmute(text.0), &self.0, ptr::null(), 0) }
  }
}

impl ops::Drop for RE2 {
  fn drop(&mut self) {
    unsafe {
      /* self.0.destruct(); */
    }
  }
}

/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::re2;

use std::os::raw::c_uint;

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
    assert!(max_mem_ >= 0);
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
    static_assertions::const_assert!(re2::RE2_Options_kDefaultMaxMem >= 0);
    Self {
      max_mem: re2::RE2_Options_kDefaultMaxMem as u32,
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

#[derive(
  Debug,
  Default,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::TryFromPrimitive,
  num_enum::IntoPrimitive,
)]
#[repr(u32)]
pub enum Anchor {
  /// unanchored
  #[default]
  Unanchored = re2::RE2_Anchor_UNANCHORED,
  /// anchored at start
  AnchorStart = re2::RE2_Anchor_ANCHOR_START,
  /// anchored at both start and end
  AnchorBoth = re2::RE2_Anchor_ANCHOR_BOTH,
}

impl Anchor {
  #[inline]
  pub fn into_native(self) -> c_uint { self.into() }
}

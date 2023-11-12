/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::re2;

use displaydoc::Display;
use thiserror::Error;

#[derive(
  Debug,
  Display,
  Error,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::IntoPrimitive,
  num_enum::FromPrimitive,
)]
#[repr(u32)]
pub enum RE2ErrorCode {
  /// Unexpected error
  Internal = re2::RE2_ErrorCode_ErrorInternal,
  /// bad escape sequence
  BadEscape = re2::RE2_ErrorCode_ErrorBadEscape,
  /// bad character class
  BadCharClass = re2::RE2_ErrorCode_ErrorBadCharClass,
  /// bad character class range
  BadCharRange = re2::RE2_ErrorCode_ErrorBadCharRange,
  /// missing closing ']'
  MissingBracket = re2::RE2_ErrorCode_ErrorMissingBracket,
  /// missing closing ')'
  MissingParen = re2::RE2_ErrorCode_ErrorMissingParen,
  /// unexpected closing ')'
  UnexpectedParen = re2::RE2_ErrorCode_ErrorUnexpectedParen,
  /// trailing '\' at end of regexp
  TrailingBackslash = re2::RE2_ErrorCode_ErrorTrailingBackslash,
  /// repeat argument missing, e.g. "*"
  RepeatArgument = re2::RE2_ErrorCode_ErrorRepeatArgument,
  /// bad repetition argument
  RepeatSize = re2::RE2_ErrorCode_ErrorRepeatSize,
  /// bad repetition operator
  RepeatOp = re2::RE2_ErrorCode_ErrorRepeatOp,
  /// bad perl operator
  BadPerlOp = re2::RE2_ErrorCode_ErrorBadPerlOp,
  /// invalid UTF-8 in regexp
  BadUTF8 = re2::RE2_ErrorCode_ErrorBadUTF8,
  /// bad named capture group
  BadNamedCapture = re2::RE2_ErrorCode_ErrorBadNamedCapture,
  /// pattern too large (compile failed)
  PatternTooLarge = re2::RE2_ErrorCode_ErrorPatternTooLarge,
  /// unknown error (not within re2 spec)
  #[num_enum(default)]
  UnknownError = 300,
}

impl RE2ErrorCode {
  #[inline]
  pub(crate) fn from_native(x: re2::RE2_ErrorCode) -> Result<(), Self> {
    static_assertions::const_assert_eq!(0, re2::RE2_ErrorCode_NoError);
    if x == 0 {
      Ok(())
    } else {
      let s: Self = (x as u32).into();
      Err(s)
    }
  }
}

/// compile error({code}): {message}({arg})
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub struct CompileError {
  pub message: String,
  pub arg: String,
  #[source]
  pub code: RE2ErrorCode,
}

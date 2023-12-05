/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::re2;

use displaydoc::Display;
use thiserror::Error;

use std::os::raw::c_uint;

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
      let s: Self = (x as c_uint).into();
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

/// rewrite error: {message}
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub struct RewriteError {
  pub message: String,
}

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
pub enum SetErrorKind {
  /// not compiled
  NotCompiled = re2::RE2_Set_ErrorKind_kNotCompiled,
  /// out of memory
  OutOfMemory = re2::RE2_Set_ErrorKind_kOutOfMemory,
  /// inconsistent
  Inconsistent = re2::RE2_Set_ErrorKind_kInconsistent,
  /// unknown error (not within re2 spec)
  #[num_enum(default)]
  UnknownError = 300,
}

impl SetErrorKind {
  #[inline]
  pub(crate) fn from_native(x: re2::RE2_Set_ErrorKind) -> Result<(), Self> {
    static_assertions::const_assert_eq!(0, re2::RE2_Set_ErrorKind_kNoError);
    if x == 0 {
      Ok(())
    } else {
      let s: Self = (x as c_uint).into();
      Err(s)
    }
  }
}

/// set error kind={kind}
#[derive(Debug, Display, Error, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SetErrorInfo {
  #[from]
  pub kind: SetErrorKind,
}

impl SetErrorInfo {
  #[inline]
  pub(crate) fn from_native(x: re2::RE2_Set_ErrorInfo) -> Result<(), Self> {
    let re2::RE2_Set_ErrorInfo { kind } = x;
    SetErrorKind::from_native(kind)?;
    Ok(())
  }
}

/// error parsing pattern for set: {message}
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub struct SetPatternError {
  pub message: String,
}

#[derive(Debug, Display, Error, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SetCompileError {
  /// out of memory
  OutOfMemory,
}

#[derive(Debug, Display, Error)]
pub enum RE2Error {
  /// re2 runtime error: {0}
  Runtime(#[from] RE2ErrorCode),
  /// pattern compilation error: {0}
  Compile(#[from] CompileError),
  /// error rewriting string: {0}
  Rewrite(#[from] RewriteError),
  /// error in set compilation: {0}
  Set(#[from] SetErrorInfo),
  /// error in set pattern: {0}
  SetPattern(#[from] SetPatternError),
  /// error compiling set: {0}
  SetCompile(#[from] SetCompileError),
}

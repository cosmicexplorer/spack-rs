/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Error codes and additional data.
//!
//! [`RE2`](crate::RE2) objects don't produce [`Result`] objects when matching,
//! preferring to simply return [`bool`] or [`Option`]. Instead, errors
//! typically occur during compilation of different types of patterns, with the
//! exception of [`SetErrorInfo`] which is returned by
//! [`Set::match_routine_with_error()`](crate::set::Set::match_routine_with_error).

use crate::re2;

use displaydoc::Display;
use thiserror::Error;

use std::os::raw::c_uint;

/// Basic error code for compile failures, corresponding to a C++ enum.
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
  /// error message
  pub message: String,
  /// pattern string that produced the error
  pub arg: String,
  /// underlying error code
  #[source]
  pub code: RE2ErrorCode,
}

/// rewrite error: {message}
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub struct RewriteError {
  /// error message
  pub message: String,
}

/// Error compiling a set of patterns.
#[derive(Debug, Display, Error)]
pub enum SetError {
  /// error in set matching: {0}
  Runtime(#[from] SetErrorInfo),
  /// error in set pattern: {0}
  Pattern(#[from] SetPatternError),
  /// error compiling set: {0}
  SetCompile(#[from] SetCompileError),
}

/// Basic error code for set matching failures, corresponding to a C++ enum.
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
  /// underlying error code
  #[from]
  pub kind: SetErrorKind,
}

impl SetErrorInfo {
  pub(crate) fn from_native(x: re2::RE2_Set_ErrorInfo) -> Result<(), Self> {
    let re2::RE2_Set_ErrorInfo { kind } = x;
    SetErrorKind::from_native(kind)?;
    Ok(())
  }
}

/// error parsing pattern for set: {message}
#[derive(Debug, Display, Error, PartialEq, Eq, Hash)]
pub struct SetPatternError {
  /// error message
  pub message: String,
}

/// Errors compiling a set of patterns.
#[derive(Debug, Display, Error, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SetCompileError {
  /// out of memory
  OutOfMemory,
}

/// Top-level catch-all error for all types of failures in this crate.
#[derive(Debug, Display, Error)]
pub enum RE2Error {
  /// re2 runtime error: {0}
  Runtime(#[from] RE2ErrorCode),
  /// pattern compilation error: {0}
  Compile(#[from] CompileError),
  /// error rewriting string: {0}
  Rewrite(#[from] RewriteError),
  /// set error: {0}
  Set(#[from] SetError),
}

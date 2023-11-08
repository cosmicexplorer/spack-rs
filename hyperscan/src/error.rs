/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{hs, ExpressionIndex};

use displaydoc::Display;
use thiserror::Error;

use std::{ffi::CStr, os::raw::c_uint};

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
#[repr(i8)]
#[ignore_extra_doc_attributes]
pub enum HyperscanError {
  /// A parameter passed to this function was invalid.
  ///
  /// This error is only returned in cases where the function can detect an
  /// invalid parameter -- it cannot be relied upon to detect (for example)
  /// pointers to freed memory or other invalid data.
  Invalid = hs::HS_INVALID,
  /// A memory allocation failed.
  NoMem = hs::HS_NOMEM,
  /// The engine was terminated by callback.
  ///
  /// This return value indicates that the target buffer was partially scanned,
  /// but that the callback function requested that scanning cease after a match
  /// was located.
  ScanTerminated = hs::HS_SCAN_TERMINATED,
  /// The pattern compiler failed, and the [`CompileError`] should be
  /// inspected for more detail.
  CompilerError = hs::HS_COMPILER_ERROR,
  /// The given database was built for a different version of Hyperscan.
  DbVersionError = hs::HS_DB_VERSION_ERROR,
  /// The given database was built for a different platform (i.e., CPU type).
  DbPlatformError = hs::HS_DB_PLATFORM_ERROR,
  /// The given database was built for a different mode of operation.
  ///
  /// This error is returned when streaming calls are used with a block or
  /// vectored database and vice versa.
  DbModeError = hs::HS_DB_MODE_ERROR,
  /// A parameter passed to this function was not correctly aligned.
  BadAlign = hs::HS_BAD_ALIGN,
  /// The memory allocator returned incorrectly aligned memory.
  ///
  /// The memory allocator (either `malloc()` or the allocator set with @ref
  /// hs_set_allocator()) did not correctly return memory suitably aligned for
  /// the largest representable data type on this platform.
  BadAlloc = hs::HS_BAD_ALLOC,
  /// The scratch region was already in use.
  ///
  /// This error is returned when Hyperscan is able to detect that the scratch
  /// region given is already in use by another Hyperscan API call.
  ///
  /// A separate scratch region, allocated with @ref hs_alloc_scratch() or @ref
  /// hs_clone_scratch(), is required for every concurrent caller of the
  /// Hyperscan API.
  ///
  /// For example, this error might be returned when @ref hs_scan() has been
  /// called inside a callback delivered by a currently-executing @ref hs_scan()
  /// call using the same scratch region.
  ///
  /// Note: Not all concurrent uses of scratch regions may be detected. This
  /// error is intended as a best-effort debugging tool, not a guarantee.
  ScratchInUse = hs::HS_SCRATCH_IN_USE,
  /// Unsupported CPU architecture.
  ///
  /// This error is returned when Hyperscan is able to detect that the current
  /// system does not support the required instruction set.
  ///
  /// At a minimum, Hyperscan requires Supplemental Streaming SIMD Extensions 3
  /// (SSSE3).
  ArchError = hs::HS_ARCH_ERROR,
  /// Provided buffer was too small.
  ///
  /// This error indicates that there was insufficient space in the buffer. The
  /// call should be repeated with a larger provided buffer.
  ///
  /// Note: in this situation, it is normal for the amount of space required to
  /// be returned in the same manner as the used space would have been
  /// returned if the call was successful.
  InsufficientSpace = hs::HS_INSUFFICIENT_SPACE,
  /// Unexpected internal error.
  ///
  /// This error indicates that there was unexpected matching behaviors. This
  /// could be related to invalid usage of stream and scratch space or invalid
  /// memory operations by users.
  #[num_enum(default)]
  UnknownError = hs::HS_UNKNOWN_ERROR,
}

impl HyperscanError {
  #[inline]
  pub fn from_native(x: hs::hs_error_t) -> Result<(), Self> {
    static_assertions::const_assert_eq!(0, hs::HS_SUCCESS);
    if x == 0 {
      Ok(())
    } else {
      let s: Self = (x as i8).into();
      Err(s)
    }
  }

  #[inline]
  pub fn copy_from_native_compile_error(
    x: hs::hs_error_t,
    c: *mut hs::hs_compile_error,
  ) -> Result<(), HyperscanCompileError> {
    match Self::from_native(x) {
      Ok(()) => Ok(()),
      Err(Self::CompilerError) => {
        let e = CompileError::copy_from_native(unsafe { &mut *c }).unwrap();
        Err(HyperscanCompileError::Compile(e))
      },
      Err(e) => Err(e.into()),
    }
  }
}

#[derive(Debug, Display, Error)]
pub enum HyperscanFlagsError {
  /// A mode was created without BLOCK, STREAM, or VECTORED somehow.
  InvalidDbMode,
  /// SOM_LEFTMOST flag provided, but no SOM_HORIZON_* mode was specified.
  SomHorizonModeRequired,
}

/// compile error(@{expression}): {message}
#[derive(Debug, Display, Error)]
pub struct CompileError {
  pub message: String,
  pub expression: ExpressionIndex,
}

impl CompileError {
  #[inline]
  pub fn copy_from_native(x: &mut hs::hs_compile_error) -> Result<Self, HyperscanError> {
    let hs::hs_compile_error {
      message,
      expression,
    } = x;
    assert!(!message.is_null());
    let ret = Self {
      message: unsafe { CStr::from_ptr(*message) }
        .to_string_lossy()
        .to_string(),
      expression: ExpressionIndex(*expression as c_uint),
    };
    HyperscanError::from_native(unsafe { hs::hs_free_compile_error(x) })?;
    Ok(ret)
  }
}

#[derive(Debug, Display, Error)]
pub enum HyperscanCompileError {
  /// flags error: {0}
  Flags(#[from] HyperscanFlagsError),
  /// non-compilation error: {0}
  NonCompile(#[from] HyperscanError),
  /// pattern compilation error: {0}
  Compile(#[from] CompileError),
}

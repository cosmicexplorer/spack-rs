/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::hs;
#[cfg(feature = "compile")]
use crate::matchers::ExpressionIndex;

use displaydoc::Display;
use thiserror::Error;

#[cfg(feature = "compile")]
use std::{
  ffi::{CStr, NulError},
  os::raw::c_uint,
};

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
pub enum HyperscanRuntimeError {
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

impl HyperscanRuntimeError {
  pub(crate) fn from_native(x: hs::hs_error_t) -> Result<(), Self> {
    static_assertions::const_assert_eq!(0, hs::HS_SUCCESS);
    if x == 0 {
      Ok(())
    } else {
      let s: Self = (x as i8).into();
      Err(s)
    }
  }

  #[cfg(feature = "compile")]
  pub(crate) fn copy_from_native_compile_error(
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

/// compile error(@{expression:?}): {message}
#[cfg(feature = "compile")]
#[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
#[derive(Debug, Display, Error)]
#[ignore_extra_doc_attributes]
pub struct CompileError {
  pub message: String,
  pub expression: Option<ExpressionIndex>,
}

#[cfg(feature = "compile")]
impl CompileError {
  pub(crate) fn copy_from_native(
    x: &mut hs::hs_compile_error,
  ) -> Result<Self, HyperscanRuntimeError> {
    let hs::hs_compile_error {
      message,
      expression,
    } = x;
    assert!(!message.is_null());
    let ret = Self {
      message: unsafe { CStr::from_ptr(*message) }
        .to_string_lossy()
        .to_string(),
      expression: if *expression < 0 {
        None
      } else {
        Some(ExpressionIndex(*expression as c_uint))
      },
    };
    HyperscanRuntimeError::from_native(unsafe { hs::hs_free_compile_error(x) })?;
    Ok(ret)
  }
}

#[cfg(feature = "compile")]
#[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
#[derive(Debug, Display, Error)]
pub enum HyperscanCompileError {
  /// non-compilation error: {0}
  NonCompile(#[from] HyperscanRuntimeError),
  /// pattern compilation error: {0}
  Compile(#[from] CompileError),
  /// null byte in expression: {0}
  NullByte(#[from] NulError),
}

#[derive(Debug, Display, Error)]
pub enum CompressionError {
  /// other error: {0}
  Other(#[from] HyperscanRuntimeError),
  /// not enough space for {0} in buf
  NoSpace(usize),
}

#[derive(Debug, Display, Error)]
#[ignore_extra_doc_attributes]
pub enum HyperscanError {
  /// error from the hyperscan runtime: {0}
  Runtime(#[from] HyperscanRuntimeError),
  /// compile error: {0}
  #[cfg(feature = "compile")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
  Compile(#[from] HyperscanCompileError),
  /// error compressing stream: {0}
  Compression(#[from] CompressionError),
}

#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;

  use std::{os::raw::c_void, ptr};

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
  pub enum ChimeraRuntimeError {
    /// A parameter passed to this function was invalid.
    Invalid = hs::CH_INVALID,
    /// A memory allocation failed.
    NoMem = hs::CH_NOMEM,
    /// The engine was terminated by callback.
    ///
    /// This return value indicates that the target buffer was partially
    /// scanned, but that the callback function requested that scanning
    /// cease after a match was located.
    ScanTerminated = hs::CH_SCAN_TERMINATED,
    /// The pattern compiler failed, and the @ref ch_compile_error_t should be
    /// inspected for more detail.
    CompilerError = hs::CH_COMPILER_ERROR,
    /// The given database was built for a different version of the Chimera
    /// matcher.
    DbVersionError = hs::CH_DB_VERSION_ERROR,
    /// The given database was built for a different platform (i.e., CPU type).
    DbPlatformError = hs::CH_DB_PLATFORM_ERROR,
    /// The given database was built for a different mode of operation.
    ///
    /// This error is returned when streaming calls are used with a
    /// non-streaming database and vice versa.
    DbModeError = hs::CH_DB_MODE_ERROR,
    /// A parameter passed to this function was not correctly aligned.
    BadAlign = hs::CH_BAD_ALIGN,
    /// The memory allocator did not correctly return memory suitably aligned
    /// for the largest representable data type on this platform.
    BadAlloc = hs::CH_BAD_ALLOC,
    /// The scratch region was already in use.
    ///
    /// This error is returned when Chimera is able to detect that the scratch
    /// region given is already in use by another Chimera API call.
    ///
    /// A separate scratch region, allocated with @ref ch_alloc_scratch() or
    /// @ref ch_clone_scratch(), is required for every concurrent caller of
    /// the Chimera API.
    ///
    /// For example, this error might be returned when @ref ch_scan() has been
    /// called inside a callback delivered by a currently-executing @ref
    /// ch_scan() call using the same scratch region.
    ///
    /// Note: Not all concurrent uses of scratch regions may be detected. This
    /// error is intended as a best-effort debugging tool, not a guarantee.
    ScratchInUse = hs::CH_SCRATCH_IN_USE,
    /// Unexpected internal error from Hyperscan.
    ///
    /// This error indicates that there was unexpected matching behaviors from
    /// Hyperscan. This could be related to invalid usage of scratch space or
    /// invalid memory operations by users.
    #[num_enum(default)]
    UnknownError = hs::CH_UNKNOWN_HS_ERROR,
    /// Returned when pcre_exec (called for some expressions internally from
    /// @ref ch_scan) failed due to a fatal error.
    FailInternal = hs::CH_FAIL_INTERNAL,
  }

  impl ChimeraRuntimeError {
    pub(crate) fn from_native(x: hs::ch_error_t) -> Result<(), Self> {
      static_assertions::const_assert_eq!(0, hs::CH_SUCCESS);
      if x == 0 {
        Ok(())
      } else {
        let s: Self = (x as i8).into();
        Err(s)
      }
    }

    pub(crate) fn copy_from_native_compile_error(
      x: hs::ch_error_t,
      c: *mut hs::ch_compile_error,
    ) -> Result<(), ChimeraCompileError> {
      match Self::from_native(x) {
        Ok(()) => Ok(()),
        Err(Self::CompilerError) => {
          let e = ChimeraInnerCompileError::copy_from_native(unsafe { &mut *c }).unwrap();
          Err(ChimeraCompileError::Compile(e))
        },
        Err(e) => Err(e.into()),
      }
    }
  }

  /// compile error(@{expression:?}): {message}
  #[derive(Debug, Display, Error)]
  pub struct ChimeraInnerCompileError {
    pub message: String,
    pub expression: Option<ExpressionIndex>,
  }

  impl ChimeraInnerCompileError {
    pub(crate) fn copy_from_native(
      x: &mut hs::ch_compile_error,
    ) -> Result<Self, ChimeraRuntimeError> {
      let hs::ch_compile_error {
        message,
        expression,
      } = x;
      assert!(!message.is_null());
      let ret = Self {
        message: unsafe { CStr::from_ptr(*message) }
          .to_string_lossy()
          .to_string(),
        expression: if *expression < 0 {
          None
        } else {
          Some(ExpressionIndex(*expression as c_uint))
        },
      };
      ChimeraRuntimeError::from_native(unsafe { hs::ch_free_compile_error(x) })?;
      Ok(ret)
    }
  }

  #[derive(Debug, Display, Error)]
  pub enum ChimeraCompileError {
    /// non-compilation error: {0}
    NonCompile(#[from] ChimeraRuntimeError),
    /// pattern compilation error: {0}
    Compile(#[from] ChimeraInnerCompileError),
    /// null byte in expression: {0}
    NullByte(#[from] NulError),
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
    num_enum::TryFromPrimitive,
  )]
  #[repr(u8)]
  pub enum ChimeraMatchErrorType {
    /// PCRE hits its match limit and reports PCRE_ERROR_MATCHLIMIT.
    MatchLimit = hs::CH_ERROR_MATCHLIMIT,
    /// PCRE hits its recursion limit and reports PCRE_ERROR_RECURSIONLIMIT.
    RecursionLimit = hs::CH_ERROR_RECURSIONLIMIT,
  }

  impl ChimeraMatchErrorType {
    pub(crate) fn from_native(x: hs::ch_error_event_t) -> Self { (x as u8).try_into().unwrap() }
  }

  /// {error_type}@{id}(info={info:?})
  #[derive(Debug, Display, Error)]
  pub struct ChimeraMatchError {
    #[source]
    pub error_type: ChimeraMatchErrorType,
    pub id: ExpressionIndex,
    pub info: Option<ptr::NonNull<c_void>>,
  }

  unsafe impl Send for ChimeraMatchError {}

  #[derive(Debug, Display, Error)]
  pub enum ChimeraScanError {
    /// error from return value of ch_scan: {0}
    ReturnValue(#[from] ChimeraRuntimeError),
    /// streaming pcre error: {0}
    MatchError(#[from] ChimeraMatchError),
    /// join error: {0}
    Join(#[from] tokio::task::JoinError),
  }

  #[derive(Debug, Display, Error)]
  pub enum ChimeraError {
    /// error from chimera runtime: {0}
    Runtime(#[from] ChimeraRuntimeError),
    /// compile error: {0}
    Compile(#[from] ChimeraCompileError),
    /// error during chimera scan: {0}
    Scan(#[from] ChimeraScanError),
  }
}

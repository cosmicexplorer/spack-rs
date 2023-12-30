/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Errors returned by methods in this library.

use crate::hs;
#[cfg(feature = "compiler")]
use crate::matchers::ExpressionIndex;

use displaydoc::Display;
use thiserror::Error;

#[cfg(feature = "compiler")]
use std::{
  ffi::{CStr, NulError},
  fmt,
  os::raw::c_uint,
};

/// Native error code from the underlying hyperscan library.
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
  /// but that the callback function returned
  /// [`MatchResult::CeaseMatching`](crate::matchers::MatchResult::CeaseMatching)
  /// after a match was located.
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
  /// The memory allocator (either [`libc::malloc()`] or the allocator set with
  /// [`crate::alloc::set_allocator()`]) did not
  /// correctly return memory suitably aligned for the largest representable
  /// data type on this platform.
  BadAlloc = hs::HS_BAD_ALLOC,
  /// The scratch region was already in use.
  ///
  /// This error is returned when Hyperscan is able to detect that the scratch
  /// region given is already in use by another Hyperscan API call.
  ///
  /// A separate scratch region, allocated with
  /// [`Scratch::setup_for_db()`](crate::state::Scratch::setup_for_db) or
  /// [`Scratch::try_clone()`](crate::state::Scratch::try_clone), is required
  /// for every concurrent caller of the Hyperscan API.
  ///
  /// For example, this error might be returned when
  /// [`scan_sync()`](crate::state::Scratch::scan_sync) has been
  /// called inside a callback delivered by a currently-executing
  /// [`scan_sync()`](crate::state::Scratch::scan_sync) call using the same
  /// scratch region.
  ///
  /// Note: Not all concurrent uses of scratch regions may be detected. This
  /// error is intended as a best-effort debugging tool, not a guarantee.
  ///
  /// Note: safe Rust code should never see this error.
  /// [`Arc::make_mut()`](std::sync::Arc::make_mut) is often an effective way to
  /// avoid this while preserving the ergonomics of a [`Clone`] and [`Send`]
  /// reference type.
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
  ///
  /// This value is referenced internally in
  /// [`LiveStream::compress()`](crate::stream::LiveStream) when requesting the
  /// amount of memory to allocate for a compressed stream. Users of this
  /// library should never see this error when using the
  /// [`CompressReserveBehavior`](crate::stream::compress::CompressReserveBehavior)
  /// interface.
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

  #[cfg(feature = "compiler")]
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

/// Error details returned by the pattern compiler.
///
/// This is returned by the compile calls
/// ([`Database::compile()`](crate::database::Database::compile) and
/// [`Database::compile_multi()`](crate::database::Database::compile_multi)) on
/// failure. The caller may inspect the values returned in this type to
/// determine the cause of failure.
#[cfg(feature = "compiler")]
#[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
#[derive(Debug, Error)]
pub struct CompileError {
  /// A human-readable error message describing the error.
  ///
  /// # Common Errors
  /// Common errors generated during the compile process include:
  ///
  /// - *Invalid parameter:* An invalid argument was specified in the compile
  ///   call.
  ///
  /// - *Unrecognised flag:* An unrecognised value was passed in the flags
  ///   argument.
  ///
  /// - *Pattern matches empty buffer:* By default, Hyperscan only supports
  ///   patterns that will *always* consume at least one byte of input. Patterns
  ///   that do not have this property (such as `/(abc)?/`) will produce this
  ///   error unless the [`Flags::ALLOWEMPTY`](crate::flags::Flags::ALLOWEMPTY)
  ///   flag is supplied. Note that such patterns will produce a match for
  ///   *every* byte when scanned.
  ///
  /// - *Embedded anchors not supported:* Hyperscan only supports the use of
  ///   anchor meta-characters (such as `^` and `$`) in patterns where they
  ///   could *only* match at the start or end of a buffer. A pattern containing
  ///   an embedded anchor, such as `/abc^def/`, can never match, as there is no
  ///   way for `abc` to precede the start of the data stream.
  ///
  /// - *Bounded repeat is too large:* The pattern contains a repeated construct
  ///   with very large finite bounds.
  ///
  /// - *Unsupported component type:* An unsupported PCRE construct was used in
  ///   the pattern. Consider using [`chimera`](crate::expression::chimera) for
  ///   full PCRE support.
  ///
  /// - *Unable to generate bytecode:* This error indicates that Hyperscan was
  ///   unable to compile a pattern that is syntactically valid. The most common
  ///   cause is a pattern that is very long and complex or contains a large
  ///   repeated subpattern.
  ///
  /// - *Unable to allocate memory:* The library was unable to allocate
  ///   temporary storage used during compilation time.
  ///
  /// - *Allocator returned misaligned memory:* The memory allocator (either
  ///   [`libc::malloc()`] or the allocator set with
  ///   [`set_db_allocator()`](crate::alloc::set_db_allocator)) did not
  ///   correctly return memory suitably aligned for the largest representable
  ///   data type on this platform.
  ///
  /// - *Internal error:* An unexpected error occurred: if this error is
  ///   reported, please contact the Hyperscan team with a description of the
  ///   situation.
  pub message: String,
  /// The zero-based number of the expression that caused the error (if this
  /// can be determined). For a database with a single expression, this value
  /// will be `0`:
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, error::*, matchers::*, flags::*};
  ///
  /// let expr: Expression = "as(df".parse()?;
  /// let index = match expr.compile(Flags::default(), Mode::BLOCK) {
  ///   Err(HyperscanCompileError::Compile(CompileError { expression, .. })) => expression,
  ///   _ => unreachable!(),
  /// };
  /// assert_eq!(index, Some(ExpressionIndex(0)));
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// Note that while this uses the same [`ExpressionIndex`] type as in
  /// [`Match`](crate::matchers::Match), the value is *not*
  /// calculated from any [`ExprId`](crate::expression::ExprId) instances
  /// provided to
  /// [`ExpressionSet::with_ids()`](crate::expression::ExpressionSet::with_ids),
  /// but instead just from the expression's index in the set:
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, error::*, matchers::*, flags::*};
  ///
  /// let e1: Expression = "aa".parse()?;
  /// let e2: Expression = "as(df".parse()?;
  /// let set = ExpressionSet::from_exprs([&e1, &e2]).with_ids([ExprId(2), ExprId(3)]);
  /// let index = match set.compile(Mode::BLOCK) {
  ///   Err(HyperscanCompileError::Compile(CompileError { expression, .. })) => expression,
  ///   _ => unreachable!(),
  /// };
  /// assert_eq!(index, Some(ExpressionIndex(1)));
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// If the error is not specific to an expression, then this value will be
  /// [`None`]:
  ///```
  /// // Using hyperscan::alloc requires the "alloc" feature.
  /// #[cfg(feature = "alloc")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, error::*, flags::*, alloc::*};
  ///   use std::{alloc::{GlobalAlloc, Layout}, ptr};
  ///
  ///   // Create a broken allocator:
  ///   struct S;
  ///   unsafe impl GlobalAlloc for S {
  ///     unsafe fn alloc(&self, _layout: Layout) -> *mut u8 { ptr::null_mut() }
  ///     unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
  ///   }
  ///   // Set it as the db compile allocator:
  ///   assert!(set_db_allocator(LayoutTracker::new(S.into())).unwrap().is_none());
  ///
  ///   let expr: Expression = "a".parse()?;
  ///   let CompileError { message, expression } = match expr.compile(Flags::default(), Mode::BLOCK) {
  ///     Err(HyperscanCompileError::Compile(err)) => err,
  ///     _ => unreachable!(),
  ///   };
  ///   assert_eq!(expression, None);
  ///   assert_eq!(&message, "Could not allocate memory for bytecode.");
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "alloc"))]
  /// # fn main() {}
  /// ```
  pub expression: Option<ExpressionIndex>,
}

#[cfg(feature = "compiler")]
impl fmt::Display for CompileError {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "compile error(@{:?}): {}",
      &self.expression, &self.message
    )
  }
}

#[cfg(feature = "compiler")]
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

/// Wrapper for errors returned when parsing or compiling expressions.
#[cfg(feature = "compiler")]
#[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
#[derive(Debug, Display, Error)]
pub enum HyperscanCompileError {
  /// non-compilation error: {0}
  NonCompile(#[from] HyperscanRuntimeError),
  /// pattern compilation error: {0}
  Compile(#[from] CompileError),
  /// null byte in expression: {0}
  NullByte(#[from] NulError),
}

/// Failure to compress a stream into a buffer.
#[derive(Debug, Display, Error)]
pub enum CompressionError {
  /// other error: {0}
  Other(#[from] HyperscanRuntimeError),
  /// not enough space for {0} in buf {1:?}
  NoSpace(usize, Vec<u8>),
}

/// Wrapper for errors returned by
/// [`Scratch::scan_channel()`](crate::state::Scratch::scan_channel) and other
/// async scanning methods.
#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
#[derive(Debug, Display, Error)]
pub enum ScanError {
  /// error from return value of `hs_scan*()`: {0}
  ReturnValue(#[from] HyperscanRuntimeError),
  /// task join error: {0}
  Join(#[from] tokio::task::JoinError),
}

/// Top-level wrapper for errors returned by this library.
#[derive(Debug, Display, Error)]
#[ignore_extra_doc_attributes]
pub enum HyperscanError {
  /// error from the hyperscan runtime: {0}
  Runtime(#[from] HyperscanRuntimeError),
  /// compile error: {0}
  #[cfg(feature = "compiler")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
  Compile(#[from] HyperscanCompileError),
  /// error during scan: {0}
  #[cfg(feature = "async")]
  #[cfg_attr(docsrs, doc(cfg(feature = "async")))]
  Scan(#[from] ScanError),
  /// error compressing stream: {0}
  Compression(#[from] CompressionError),
}

/// Errors returned by methods in the chimera library.
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use crate::{hs, matchers::ExpressionIndex};

  use displaydoc::Display;
  use thiserror::Error;

  use std::{
    ffi::{CStr, NulError},
    fmt,
    os::raw::c_uint,
  };

  /// Native error code from the underlying chimera library.
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
    /// scanned, but that the callback function returned
    /// [`ChimeraMatchResult::Terminate`](crate::matchers::chimera::ChimeraMatchResult::Terminate)
    /// after a match was located.
    ScanTerminated = hs::CH_SCAN_TERMINATED,
    /// The pattern compiler failed, and the [`ChimeraInnerCompileError`] should
    /// be inspected for more detail.
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
    /// A separate scratch region, allocated with
    /// [`ChimeraScratch::setup_for_db()`](crate::state::chimera::ChimeraScratch::setup_for_db)
    /// or [`ChimeraScratch::try_clone()`](crate::state::chimera::ChimeraScratch::try_clone), is
    /// required for every concurrent caller of the Chimera API.
    ///
    /// For example, this error might be returned when
    /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync)
    /// has been called inside a callback delivered by a currently-executing
    /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync)
    /// call using the same scratch region.
    ///
    /// Note: Not all concurrent uses of scratch regions may be detected. This
    /// error is intended as a best-effort debugging tool, not a guarantee.
    ///
    /// Note: safe Rust code should never see this error.
    /// [`Arc::make_mut()`](std::sync::Arc::make_mut) is often an effective way
    /// to avoid this while preserving the ergonomics of a [`Clone`] and
    /// [`Send`] reference type.
    ScratchInUse = hs::CH_SCRATCH_IN_USE,
    /// Unexpected internal error from Hyperscan.
    ///
    /// This error indicates that there was unexpected matching behaviors from
    /// Hyperscan. This could be related to invalid usage of scratch space or
    /// invalid memory operations by users.
    #[num_enum(default)]
    UnknownError = hs::CH_UNKNOWN_HS_ERROR,
    /// Returned when pcre_exec (called for some expressions internally from
    /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync))
    /// failed due to a fatal error.
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

    #[cfg(feature = "compiler")]
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

  /// Error details returned by the pattern compiler.
  ///
  /// This is returned by the compile calls
  /// ([`ChimeraDb::compile()`](crate::database::chimera::ChimeraDb::compile)
  /// and [`ChimeraDb::compile_multi()`](crate::database::chimera::ChimeraDb::compile_multi)) on
  /// failure. The caller may inspect the values returned in this type to
  /// determine the cause of failure.
  #[derive(Debug, Error)]
  #[cfg(feature = "compiler")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
  pub struct ChimeraInnerCompileError {
    /// A human-readable error message describing the error.
    ///
    /// Common errors are the same as for the base hyperscan library's
    /// [`super::CompileError::message`], except that PCRE constructs are fully
    /// supported and will not cause errors.
    pub message: String,
    /// The zero-based number of the expression that caused the error (if this
    /// can be determined). This value's behavior is the same as for the base
    /// hyperscan library's [`super::CompileError::expression`].
    pub expression: Option<ExpressionIndex>,
  }

  #[cfg(feature = "compiler")]
  impl fmt::Display for ChimeraInnerCompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      write!(
        f,
        "chimera compile error(@{:?}): {}",
        &self.expression, &self.message
      )
    }
  }

  #[cfg(feature = "compiler")]
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

  /// Wrapper for errors returned when parsing or compiling expressions.
  #[cfg(feature = "compiler")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
  #[derive(Debug, Display, Error)]
  pub enum ChimeraCompileError {
    /// non-compilation error: {0}
    NonCompile(#[from] ChimeraRuntimeError),
    /// pattern compilation error: {0}
    Compile(#[from] ChimeraInnerCompileError),
    /// null byte in expression: {0}
    NullByte(#[from] NulError),
  }

  /// Native error code for non-fatal match errors from PCRE execution.
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
    /// PCRE hits its match limit and reports `PCRE_ERROR_MATCHLIMIT`.
    MatchLimit = hs::CH_ERROR_MATCHLIMIT,
    /// PCRE hits its recursion limit and reports `PCRE_ERROR_RECURSIONLIMIT`.
    RecursionLimit = hs::CH_ERROR_RECURSIONLIMIT,
  }

  impl ChimeraMatchErrorType {
    pub(crate) fn from_native(x: hs::ch_error_event_t) -> Self { (x as u8).try_into().unwrap() }
  }

  /// Error type for non-fatal match errors from PCRE execution during
  /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync).
  #[derive(Debug, Error)]
  pub struct ChimeraMatchError {
    /// The type of error that occurred.
    #[source]
    pub error_type: ChimeraMatchErrorType,
    /// The ID number of the expression that failed.
    pub id: ExpressionIndex,
  }

  impl fmt::Display for ChimeraMatchError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      write!(f, "{}@{}", self.error_type, self.id)
    }
  }

  /// Wrapper for errors returned by
  /// [`ChimeraScratch::scan_channel()`](crate::state::chimera::ChimeraScratch::scan_channel).
  #[cfg(feature = "async")]
  #[cfg_attr(docsrs, doc(cfg(feature = "async")))]
  #[derive(Debug, Display, Error)]
  pub enum ChimeraScanError {
    /// error from return value of `ch_scan()`: {0}
    ReturnValue(#[from] ChimeraRuntimeError),
    /// non-fatal match error: {0}
    MatchError(#[from] ChimeraMatchError),
    /// task join error: {0}
    Join(#[from] tokio::task::JoinError),
  }

  /// Top-level wrapper for errors returned by the chimera library.
  #[derive(Debug, Display, Error)]
  #[ignore_extra_doc_attributes]
  pub enum ChimeraError {
    /// error from chimera runtime: {0}
    Runtime(#[from] ChimeraRuntimeError),
    /// error from hyperscan runtime: {0}
    ///
    /// This case in particular is helpful to convert the result of
    /// [`Platform::local()`](crate::flags::platform::Platform::local) into a
    /// chimera error.
    #[cfg(feature = "compiler")]
    #[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
    HyperscanRuntime(#[from] super::HyperscanRuntimeError),
    /// compile error: {0}
    #[cfg(feature = "compiler")]
    #[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
    Compile(#[from] ChimeraCompileError),
    /// error during chimera scan: {0}
    #[cfg(feature = "async")]
    #[cfg_attr(docsrs, doc(cfg(feature = "async")))]
    Scan(#[from] ChimeraScanError),
  }
}

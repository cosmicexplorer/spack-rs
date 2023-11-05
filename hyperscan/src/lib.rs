/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

#[allow(unused, non_camel_case_types)]
mod bindings;

use bindings as hs;

use displaydoc::Display;
use once_cell::sync::Lazy;
use thiserror::Error;

use std::{
  any,
  ffi::CStr,
  mem, ops,
  os::raw::{c_char, c_int, c_uint, c_void},
  ptr,
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
        let e = CompileError::copy_from_native(unsafe { &*c });
        Err(HyperscanCompileError::Compile(e))
      },
      Err(e) => Err(e.into()),
    }
  }
}

pub trait BitSet:
  Copy+ops::BitOr<Output=Self>+ops::BitOrAssign+ops::BitAnd<Output=Self>+ops::BitAndAssign
{
  fn nonzero(&self) -> bool;
  #[inline]
  fn contains(&self, other: &Self) -> bool { (*self & *other).nonzero() }
}

/// Flags which modify the behaviour of each expression. Multiple flags may be
/// used by ORing them together.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Flags(u16);

impl Flags {
  /// Allow expressions which can match against an empty string, such as `.*`.
  pub const ALLOWEMPTY: Self = Self(hs::HS_FLAG_ALLOWEMPTY as u16);
  /// Matching will be performed case-insensitively.
  pub const CASELESS: Self = Self(hs::HS_FLAG_CASELESS as u16);
  /// Parse the expression in logical combination syntax.
  pub const COMBINATION: Self = Self(hs::HS_FLAG_COMBINATION);
  /// Matching a `.` will not exclude newlines.
  pub const DOTALL: Self = Self(hs::HS_FLAG_DOTALL as u16);
  /// `^` and `$` anchors match any newlines in data.
  pub const MULTILINE: Self = Self(hs::HS_FLAG_MULTILINE as u16);
  /// Compile pattern in prefiltering mode.
  pub const PREFILTER: Self = Self(hs::HS_FLAG_PREFILTER as u16);
  /// Ignore match reporting for this expression. Used for the sub-expressions
  /// in logical combinations.
  pub const QUIET: Self = Self(hs::HS_FLAG_QUIET);
  /// Only one match will be generated by patterns with this match id per
  /// stream.
  pub const SINGLEMATCH: Self = Self(hs::HS_FLAG_SINGLEMATCH as u16);
  /// Report the leftmost start of match offset when a match is found.
  pub const SOM_LEFTMOST: Self = Self(hs::HS_FLAG_SOM_LEFTMOST);
  /// Use Unicode properties for character classes.
  pub const UCP: Self = Self(hs::HS_FLAG_UCP as u16);
  /// Treat this pattern as a sequence of UTF-8 characters.
  pub const UTF8: Self = Self(hs::HS_FLAG_UTF8 as u16);
}

impl BitSet for Flags {
  #[inline]
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for Flags {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for Flags {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for Flags {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}

impl ops::BitAndAssign for Flags {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}

#[derive(Debug, Display, Error)]
pub enum HyperscanFlagsError {
  /// A mode was created without BLOCK, STREAM, or VECTORED somehow.
  InvalidDbMode,
  /// SOM_LEFTMOST flag provided, but no SOM_HORIZON_* mode was specified.
  SomHorizonModeRequired,
}

/// Compiler mode flags that affect the database as a whole.
///
/// No [`Default`] impl is provided to enforce that at least one of
/// [`STREAM`](Self::STREAM), [`BLOCK`](Self::BLOCK), or
/// [`VECTORED`](Self::VECTORED) is supplied, to select between the generation
/// of a streaming, block or vectored database. In addition, other flags
/// (beginning with HS_MODE_) may be supplied to enable specific features. See
/// @ref HS_MODE_FLAG for more details.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Mode(u32);

static_assertions::const_assert_eq!(hs::HS_MODE_BLOCK, hs::HS_MODE_NOSTREAM);

impl Mode {
  /// Block scan (non-streaming) database.
  pub const BLOCK: Self = Self(hs::HS_MODE_BLOCK as u32);
  /// Alias for [`BLOCK`].
  pub const NOSTREAM: Self = Self(hs::HS_MODE_NOSTREAM as u32);
  /// Use full precision to track start of match offsets in stream state.
  ///
  /// This mode will use the most stream state per pattern, but will always
  /// return an accurate start of match offset regardless of how far back in
  /// the past it was found.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_LARGE: Self = Self(hs::HS_MODE_SOM_HORIZON_LARGE);
  /// Use medium precision to track start of match offsets in
  /// stream state.
  ///
  /// This mode will use less stream state than [`SOM_HORIZON_LARGE`]
  /// and will limit start of match accuracy to offsets within 2^32 bytes of
  /// the end of match offset reported.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_MEDIUM: Self = Self(hs::HS_MODE_SOM_HORIZON_MEDIUM);
  /// Use limited precision to track start of match offsets in
  /// stream state.
  ///
  /// This mode will use less stream state than [`SOM_HORIZON_LARGE`] and
  /// will limit start of match accuracy to offsets within 2^16 bytes of the
  /// end of match offset reported.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_SMALL: Self = Self(hs::HS_MODE_SOM_HORIZON_SMALL);
  /// Streaming database.
  pub const STREAM: Self = Self(hs::HS_MODE_STREAM as u32);
  /// Vectored scanning database.
  pub const VECTORED: Self = Self(hs::HS_MODE_VECTORED as u32);

  #[inline]
  fn check_db_type(&self) -> bool {
    self.contains(&Self::NOSTREAM) || self.contains(&Self::STREAM) || self.contains(&Self::VECTORED)
  }

  #[inline]
  pub fn validate_db_type(&self) -> Result<(), HyperscanFlagsError> {
    if self.check_db_type() {
      Ok(())
    } else {
      Err(HyperscanFlagsError::InvalidDbMode)
    }
  }

  #[inline]
  fn any_som_horizon_mode_was_selected(&self) -> bool {
    self.contains(&Self::SOM_HORIZON_LARGE)
      || self.contains(&Self::SOM_HORIZON_MEDIUM)
      || self.contains(&Self::SOM_HORIZON_SMALL)
  }

  #[inline]
  pub fn validate_against_flags(&self, flags: &Flags) -> Result<(), HyperscanFlagsError> {
    if flags.contains(&Flags::SOM_LEFTMOST) && !self.any_som_horizon_mode_was_selected() {
      Err(HyperscanFlagsError::SomHorizonModeRequired)
    } else {
      Ok(())
    }
  }
}

impl BitSet for Mode {
  #[inline]
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for Mode {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for Mode {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for Mode {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}

impl ops::BitAndAssign for Mode {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CpuFeatures(u8);

impl CpuFeatures {
  pub const AVX2: Self = Self(hs::HS_CPU_FEATURES_AVX2);
  pub const AVX512: Self = Self(hs::HS_CPU_FEATURES_AVX512);
  pub const AVX512VBMI: Self = Self(hs::HS_CPU_FEATURES_AVX512VBMI);
}

impl BitSet for CpuFeatures {
  #[inline]
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for CpuFeatures {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for CpuFeatures {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for CpuFeatures {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}

impl ops::BitAndAssign for CpuFeatures {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}

#[derive(
  Debug,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::FromPrimitive,
  num_enum::IntoPrimitive,
)]
#[repr(u8)]
pub enum TuneFamily {
  /// Generic
  ///
  /// This indicates that the compiled database should not be tuned for any
  /// particular target platform.
  #[num_enum(default)]
  Generic = hs::HS_TUNE_FAMILY_GENERIC,
  /// Intel(R) microarchitecture code name Sandy Bridge
  SandyBridge = hs::HS_TUNE_FAMILY_SNB,
  /// Intel(R) microarchitecture code name Ivy Bridge
  IvyBridge = hs::HS_TUNE_FAMILY_IVB,
  /// Intel(R) microarchitecture code name Haswell
  Haswell = hs::HS_TUNE_FAMILY_HSW,
  /// Intel(R) microarchitecture code name Silvermont
  Silvermont = hs::HS_TUNE_FAMILY_SLM,
  /// Intel(R) microarchitecture code name Broadwell
  Broadwell = hs::HS_TUNE_FAMILY_BDW,
  /// Intel(R) microarchitecture code name Skylake
  Skylake = hs::HS_TUNE_FAMILY_SKL,
  /// Intel(R) microarchitecture code name Skylake Server
  SkylakeServer = hs::HS_TUNE_FAMILY_SKX,
  /// Intel(R) microarchitecture code name Goldmont
  Goldmont = hs::HS_TUNE_FAMILY_GLM,
  /// Intel(R) microarchitecture code name Icelake
  Icelake = hs::HS_TUNE_FAMILY_ICL,
  /// Intel(R) microarchitecture code name Icelake Server
  IcelakeServer = hs::HS_TUNE_FAMILY_ICX,
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct Platform(pub hs::hs_platform_info);

static CACHED_PLATFORM: Lazy<Platform> = Lazy::new(|| Platform::populate().unwrap());

impl Platform {
  #[inline]
  pub fn tune(&self) -> TuneFamily { (self.0.tune as u8).into() }

  #[inline]
  pub fn set_tune(&mut self, tune: TuneFamily) {
    let tune: u8 = tune.into();
    self.0.tune = tune as u32;
  }

  #[inline]
  pub fn cpu_features(&self) -> CpuFeatures { CpuFeatures(self.0.cpu_features as u8) }

  #[inline]
  pub fn set_cpu_features(&mut self, cpu_features: CpuFeatures) {
    self.0.cpu_features = cpu_features.0 as u64;
  }

  #[inline]
  pub fn populate() -> Result<Self, HyperscanError> {
    let mut s = mem::MaybeUninit::<hs::hs_platform_info>::uninit();
    HyperscanError::from_native(unsafe { hs::hs_populate_platform(s.as_mut_ptr()) })?;
    Ok(unsafe { Self(s.assume_init()) })
  }

  #[inline]
  pub fn get() -> &'static Self { &*CACHED_PLATFORM }
}

impl AsRef<hs::hs_platform_info> for Platform {
  fn as_ref(&self) -> &hs::hs_platform_info { &self.0 }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Scratch(pub hs::hs_scratch);

impl Scratch {
  pub fn alloc(db: &Database) -> Result<Self, HyperscanError> {
    let mut scratch = mem::MaybeUninit::<hs::hs_scratch>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_alloc_scratch(db.as_ref(), mem::transmute(&mut scratch.as_mut_ptr()))
    })?;
    Ok(Self(unsafe { scratch.assume_init() }))
  }

  pub fn get_size(&self) -> Result<usize, HyperscanError> {
    let mut n = mem::MaybeUninit::<usize>::uninit();
    HyperscanError::from_native(unsafe { hs::hs_scratch_size(self.as_ref(), n.as_mut_ptr()) })?;
    Ok(unsafe { n.assume_init() })
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanError> {
    let mut scratch = mem::MaybeUninit::<hs::hs_scratch>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_clone_scratch(self.as_ref(), mem::transmute(&mut scratch.as_mut_ptr()))
    })?;
    Ok(Self(unsafe { scratch.assume_init() }))
  }

  fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_scratch(self.as_mut()) })
  }
}

impl ops::Drop for Scratch {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

impl Clone for Scratch {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl AsRef<hs::hs_scratch> for Scratch {
  fn as_ref(&self) -> &hs::hs_scratch { &self.0 }
}
impl AsMut<hs::hs_scratch> for Scratch {
  fn as_mut(&mut self) -> &mut hs::hs_scratch { &mut self.0 }
}

#[derive(Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScanFlags;

impl ScanFlags {
  #[inline]
  pub const fn into_native(self) -> c_uint { 0 }
}

/// <expression index {0}>
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub c_int);


/// compile error(@{expression}): {message}
#[derive(Debug, Display, Error)]
pub struct CompileError {
  pub message: String,
  pub expression: ExpressionIndex,
}

impl CompileError {
  #[inline]
  pub fn copy_from_native(x: &hs::hs_compile_error) -> Self {
    let hs::hs_compile_error {
      message,
      expression,
    } = x;
    assert!(!message.is_null());
    Self {
      message: unsafe { CStr::from_ptr(*message) }
        .to_string_lossy()
        .to_string(),
      expression: ExpressionIndex(*expression),
    }
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

#[derive(Debug)]
#[repr(transparent)]
pub struct Database(pub hs::hs_database);

impl AsRef<hs::hs_database> for Database {
  fn as_ref(&self) -> &hs::hs_database { &self.0 }
}

impl AsMut<hs::hs_database> for Database {
  fn as_mut(&mut self) -> &mut hs::hs_database { &mut self.0 }
}

#[repr(transparent)]
pub struct Context(pub Box<dyn any::Any>);

impl Context {
  #[inline]
  fn mut_ptr_unchecked<T: any::Any>(&mut self) -> *mut T {
    unsafe { &mut *(&mut self.0 as *mut dyn any::Any as *mut T) }
  }

  #[inline]
  pub fn as_native(&mut self) -> *mut c_void { self.mut_ptr_unchecked::<c_void>() }
}

impl Database {
  #[inline]
  fn validate_flags_and_mode(
    flags: Flags,
    mode: Mode,
  ) -> Result<(c_uint, c_uint), HyperscanFlagsError> {
    mode.validate_db_type()?;
    mode.validate_against_flags(&flags)?;
    Ok((flags.0 as c_uint, mode.0 as c_uint))
  }

  pub fn compile(
    expression: &CStr,
    flags: Flags,
    mode: Mode,
  ) -> Result<Self, HyperscanCompileError> {
    let (flags, mode) = Self::validate_flags_and_mode(flags, mode)?;
    let platform = Platform::get();
    let mut db = mem::MaybeUninit::<hs::hs_database>::uninit();
    let mut compile_err = mem::MaybeUninit::<hs::hs_compile_error>::uninit();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile(
          expression.as_ptr(),
          flags,
          mode,
          platform.as_ref(),
          mem::transmute(&mut db.as_mut_ptr()),
          mem::transmute(&mut compile_err.as_mut_ptr()),
        )
      },
      unsafe { mem::transmute(&mut compile_err) },
    )?;
    Ok(Self(unsafe { db.assume_init() }))
  }

  pub fn scan(
    &self,
    data: &[c_char],
    flags: ScanFlags,
    scratch: &mut Scratch,
    /* context: &mut Context, */
  ) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe {
      hs::hs_scan(
        self.as_ref(),
        data.as_ptr(),
        data.len() as c_uint,
        flags.into_native(),
        scratch.as_mut(),
        None,
        ptr::null_mut(),
      )
    })
  }

  pub fn scan_vector(
    &self,
    data: &[&[c_char]],
    flags: ScanFlags,
    scratch: &mut Scratch,
    /* context: &mut Context, */
  ) -> Result<(), HyperscanError> {
    let lengths: Vec<c_uint> = data.iter().map(|col| col.len() as c_uint).collect();
    HyperscanError::from_native(unsafe {
      hs::hs_scan_vector(
        self.as_ref(),
        mem::transmute(data.as_ptr()),
        lengths.as_ptr(),
        data.len() as c_uint,
        flags.into_native(),
        scratch.as_mut(),
        None,
        ptr::null_mut(),
      )
    })
  }

  #[inline]
  fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_database(self.as_mut()) })
  }
}

impl ops::Drop for Database {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

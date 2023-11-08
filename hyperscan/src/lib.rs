/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
#![feature(const_nonnull_new)]
#![feature(const_mut_refs)]
#![feature(const_pin)]

#[allow(unused, non_camel_case_types)]
mod bindings;

use bindings as hs;

use async_stream::try_stream;
use displaydoc::Display;
use futures_core::stream::Stream;
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use thiserror::Error;
use tokio::task;

use std::{
  any, cmp,
  collections::VecDeque,
  ffi::CStr,
  future::Future,
  marker::PhantomData,
  mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
  sync::Arc,
  task::{Context, Poll, Waker},
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
        let e = CompileError::copy_from_native(unsafe { &mut *c }).unwrap();
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

  pub fn try_drop(&mut self) -> Result<(), HyperscanError> {
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

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ScanFlags(c_uint);

impl ScanFlags {
  #[inline(always)]
  pub const fn from_native(x: c_uint) -> Self { Self(x) }

  #[inline(always)]
  pub const fn into_native(self) -> c_uint { self.0 }
}

/// <expression index {0}>
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub c_uint);

impl ExpressionIndex {
  pub const WHOLE_PATTERN: Self = Self(0);
}

/// <range index {0}>
#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct RangeIndex(pub c_ulonglong);

impl RangeIndex {
  #[inline(always)]
  pub const fn into_rust_index(self) -> usize {
    static_assertions::const_assert!(mem::size_of::<usize>() >= mem::size_of::<c_ulonglong>());
    self.0 as usize
  }

  #[inline(always)]
  pub const fn bounded_range(from: Self, to: Self) -> ops::Range<usize> {
    static_assertions::assert_eq_size!(ops::Range<usize>, (c_ulonglong, c_ulonglong));
    let from = from.into_rust_index();
    let to = to.into_rust_index();
    debug_assert!(from <= to);
    ops::Range {
      start: from,
      end: to,
    }
  }
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

#[derive(Debug)]
#[repr(transparent)]
pub struct Database(pub hs::hs_database);

impl AsRef<hs::hs_database> for Database {
  fn as_ref(&self) -> &hs::hs_database { &self.0 }
}

impl AsMut<hs::hs_database> for Database {
  fn as_mut(&mut self) -> &mut hs::hs_database { &mut self.0 }
}

#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
#[ignore_extra_doc_attributes]
pub enum MatchResult {
  /// Continue matching.
  Continue = 0,
  /// Immediately cease matching.
  ///
  /// If scanning is performed in streaming mode and this value is returned, any
  /// subsequent calls to @ref hs_scan_stream() for the same stream will
  /// immediately return with
  /// [`SCAN_TERMINATED`](HyperscanError::ScanTerminated).
  CeaseMatching = 1,
}

impl MatchResult {
  /* #[inline] */
  /* pub const fn */

  /* FIXME: update num_enum so they work with const fn too!!! */
  #[inline]
  pub const fn from_native(x: c_int) -> Self {
    if x == 0 {
      Self::Continue
    } else {
      Self::CeaseMatching
    }
  }

  #[inline]
  pub const fn into_native(self) -> c_int {
    match self {
      Self::Continue => 0,
      Self::CeaseMatching => 1,
    }
  }
}

#[derive(Debug)]
pub struct MatchEvent {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub flags: ScanFlags,
  pub context: Option<ptr::NonNull<c_void>>,
}

impl MatchEvent {
  #[inline(always)]
  pub const fn coerce_args(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> Self {
    static_assertions::assert_eq_size!(c_uint, ExpressionIndex);
    Self {
      id: ExpressionIndex(id),
      range: RangeIndex::bounded_range(RangeIndex(from), RangeIndex(to)),
      flags: ScanFlags::from_native(flags),
      context: ptr::NonNull::new(context),
    }
  }

  #[inline]
  pub const unsafe fn extract_context<'a, T>(
    context: Option<ptr::NonNull<c_void>>,
  ) -> Option<Pin<&'a mut T>> {
    match context {
      None => None,
      Some(c) => Some(Pin::new_unchecked(&mut *mem::transmute::<_, *mut T>(
        c.as_ptr(),
      ))),
    }
  }
}

pub type ByteSlice<'a> = &'a [c_char];

#[derive(Debug)]
pub struct Match<'a> {
  pub id: ExpressionIndex,
  pub source: ByteSlice<'a>,
  pub flags: ScanFlags,
}

pub struct SliceMatcher<'data, 'code> {
  parent_slice: ByteSlice<'data>,
  matched_slices_queue: Mutex<VecDeque<Match<'data>>>,
  handler: &'code mut dyn FnMut(&Match<'data>) -> MatchResult,
  wakers: Mutex<Vec<Waker>>,
}

impl<'data, 'code> SliceMatcher<'data, 'code> {
  #[inline]
  pub fn new<F: FnMut(&Match<'data>) -> MatchResult>(
    parent_slice: ByteSlice<'data>,
    f: &'code mut F,
  ) -> Self {
    Self {
      parent_slice,
      matched_slices_queue: Mutex::new(VecDeque::new()),
      handler: f,
      wakers: Mutex::new(Vec::new()),
    }
  }

  #[inline(always)]
  const fn parent(&self) -> ByteSlice<'data> { self.parent_slice }

  /* #[inline(always)] */
  /* pub fn is_empty(&self) -> bool { self.matched_slices_queue.is_empty() } */

  #[inline(always)]
  pub fn pop(&mut self) -> Option<Match<'data>> { self.matched_slices_queue.lock().pop_front() }

  pub fn pop_rest(&mut self) -> Vec<Match<'data>> {
    self.matched_slices_queue.lock().drain(..).collect()
  }

  #[inline(always)]
  pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> { &self.parent()[range] }

  #[inline(always)]
  pub fn push_new_match(&mut self, m: Match<'data>) {
    self.matched_slices_queue.lock().push_back(m);
    for waker in self.wakers.lock().drain(..) {
      waker.wake();
    }
  }

  /* pub fn handle_match(&self, m: Match<'data>) -> MatchResult { */
  /* let x = 3; */
  /* m */
  /* } */

  #[inline(always)]
  pub fn handle_match(&mut self, m: &Match<'data>) -> MatchResult { (self.handler)(m) }

  #[inline(always)]
  pub fn push_waker(&mut self, w: Waker) { self.wakers.lock().push(w); }
}

impl<'data, 'code> Future for SliceMatcher<'data, 'code> {
  type Output = Match<'data>;

  fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    if let Some(m) = self.pop() {
      Poll::Ready(m)
    } else {
      self.push_waker(cx.waker().clone());
      Poll::Pending
    }
  }
}

unsafe extern "C" fn match_slice_ref(
  id: c_uint,
  from: c_ulonglong,
  to: c_ulonglong,
  flags: c_uint,
  context: *mut c_void,
) -> c_int {
  let MatchEvent {
    id,
    range,
    flags,
    context,
  } = MatchEvent::coerce_args(id, from, to, flags, context);
  let mut slice_matcher: Pin<&mut SliceMatcher> =
    MatchEvent::extract_context::<'_, SliceMatcher>(context).unwrap();
  let matched_substring = slice_matcher.index_range(range);
  let m = Match {
    id,
    source: matched_substring,
    flags,
  };

  let result = slice_matcher.handle_match(&m);
  if result == MatchResult::Continue {
    slice_matcher.push_new_match(m);
  }

  result.into_native()
}

#[derive(Debug)]
pub struct VectoredMatch<'a> {
  pub id: ExpressionIndex,
  pub source: Vec<ByteSlice<'a>>,
  pub flags: ScanFlags,
}

pub struct VectoredSliceMatcher<'data, 'code> {
  parent_slices: &'data [ByteSlice<'data>],
  matched_slices_queue: Mutex<VecDeque<VectoredMatch<'data>>>,
  handler: &'code mut dyn FnMut(&VectoredMatch<'data>) -> MatchResult,
  wakers: Mutex<Vec<Waker>>,
}

impl<'data, 'code> VectoredSliceMatcher<'data, 'code> {
  #[inline]
  pub fn new<F: FnMut(&VectoredMatch<'data>) -> MatchResult>(
    parent_slices: &'data [ByteSlice<'data>],
    f: &'code mut F,
  ) -> Self {
    Self {
      parent_slices,
      matched_slices_queue: Mutex::new(VecDeque::new()),
      handler: f,
      wakers: Mutex::new(Vec::new()),
    }
  }

  #[inline(always)]
  const fn parent(&self) -> &'data [ByteSlice<'data>] { self.parent_slices }

  #[inline(always)]
  pub fn pop(&mut self) -> Option<VectoredMatch<'data>> {
    self.matched_slices_queue.lock().pop_front()
  }

  pub fn pop_rest(&mut self) -> Vec<VectoredMatch<'data>> {
    self.matched_slices_queue.lock().drain(..).collect()
  }

  fn find_index_at(
    &self,
    mut column: usize,
    mut within_column_index: usize,
    mut remaining: usize,
  ) -> Option<(usize, usize)> {
    let num_columns = self.parent().len();
    if column >= num_columns {
      return None;
    }
    if remaining == 0 {
      return Some((column, within_column_index));
    }

    let within_column_index = loop {
      let cur_col = self.parent()[column];
      let (prev, max_diff) = if within_column_index > 0 {
        let x = within_column_index;
        within_column_index = 0;
        assert_ne!(cur_col.len(), x);
        (x, cur_col.len() - x)
      } else {
        (0, cur_col.len())
      };
      assert_ne!(max_diff, 0);
      let new_offset = cmp::min(remaining, max_diff);
      let cur_ind = prev + new_offset;
      remaining -= new_offset;
      if remaining == 0 {
        break cur_ind;
      } else if column == (num_columns - 1) {
        return None;
      } else {
        column += 1;
      }
    };

    Some((column, within_column_index))
  }

  fn collect_slices_range(
    &self,
    start: (usize, usize),
    end: (usize, usize),
  ) -> Vec<ByteSlice<'data>> {
    let (start_col, start_ind) = start;
    let (end_col, end_ind) = end;
    assert!(end_col >= start_col);

    if start_col == end_col {
      assert!(end_ind >= start_ind);
      vec![&self.parent()[start_col][start_ind..end_ind]]
    } else {
      let mut ret: Vec<&'data [c_char]> = Vec::with_capacity(end_col - start_col + 1);

      ret.push(&self.parent()[start_col][start_ind..]);
      for cur_col in (start_col + 1)..end_col {
        ret.push(&self.parent()[cur_col]);
      }
      ret.push(&self.parent()[end_col][..end_ind]);
      ret
    }
  }

  pub fn index_range(&self, range: ops::Range<usize>) -> Vec<ByteSlice<'data>> {
    let ops::Range { start, end } = range;
    let (start_col, start_ind) = self.find_index_at(0, 0, start).unwrap();
    let (end_col, end_ind) = self.find_index_at(start_col, start_ind, end).unwrap();
    self.collect_slices_range((start_col, start_ind), (end_col, end_ind))
  }

  #[inline(always)]
  pub fn push_new_match(&mut self, m: VectoredMatch<'data>) {
    self.matched_slices_queue.lock().push_back(m);
    for waker in self.wakers.lock().drain(..) {
      waker.wake();
    }
  }

  #[inline(always)]
  pub fn handle_match(&mut self, m: &VectoredMatch<'data>) -> MatchResult { (self.handler)(m) }

  #[inline(always)]
  pub fn push_waker(&mut self, w: Waker) { self.wakers.lock().push(w); }
}

impl<'data, 'code> Future for VectoredSliceMatcher<'data, 'code> {
  type Output = VectoredMatch<'data>;

  fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    if let Some(m) = self.pop() {
      Poll::Ready(m)
    } else {
      self.push_waker(cx.waker().clone());
      Poll::Pending
    }
  }
}

unsafe extern "C" fn match_slice_vectored_ref(
  id: c_uint,
  from: c_ulonglong,
  to: c_ulonglong,
  flags: c_uint,
  context: *mut c_void,
) -> c_int {
  let MatchEvent {
    id,
    range,
    flags,
    context,
  } = MatchEvent::coerce_args(id, from, to, flags, context);
  let mut slice_matcher: Pin<&mut VectoredSliceMatcher> =
    MatchEvent::extract_context::<'_, VectoredSliceMatcher>(context).unwrap();
  let matched_substring = slice_matcher.index_range(range);
  let m = VectoredMatch {
    id,
    source: matched_substring,
    flags,
  };

  let result = slice_matcher.handle_match(&m);
  if result == MatchResult::Continue {
    slice_matcher.push_new_match(m);
  }

  result.into_native()
}

impl Database {
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
      compile_err.as_mut_ptr(),
    )?;
    Ok(Self(unsafe { db.assume_init() }))
  }

  pub fn scan_matches<'data, F: FnMut(&Match<'data>) -> MatchResult+'data>(
    &self,
    data: &'data [c_char],
    flags: ScanFlags,
    scratch: &mut Scratch,
    mut f: F,
  ) -> impl Stream<Item=Result<Match<'data>, HyperscanError>>+'data {
    let f: &'static mut u8 = unsafe { mem::transmute(&mut f) };
    let mut matcher = SliceMatcher::new::<F>(data, unsafe { mem::transmute(f) });

    let s: &hs::hs_database = self.as_ref();
    let s: usize = unsafe { mem::transmute(s) };
    let data_len: usize = data.len();
    let data: usize = unsafe { mem::transmute(data.as_ptr()) };
    let scratch: &mut hs::hs_scratch = scratch.as_mut();
    let scratch: usize = unsafe { mem::transmute(scratch) };

    let ctx: usize = unsafe { mem::transmute(&mut matcher) };
    let scan_task = task::spawn_blocking(move || {
      HyperscanError::from_native(unsafe {
        hs::hs_scan(
          s as *const hs::hs_database,
          data as *const c_char,
          data_len as c_uint,
          flags.into_native(),
          scratch as *mut hs::hs_scratch,
          Some(match_slice_ref),
          ctx as *mut c_void,
        )
      })
    });

    try_stream! {
      let mut matcher = Pin::new(&mut matcher);
      while !scan_task.is_finished() {
        yield matcher.as_mut().await;
      }
      for m in matcher.pop_rest().into_iter() {
        yield m;
      }
      scan_task.await.unwrap()?;
    }
  }

  pub fn scan_vector<'data, F: FnMut(&VectoredMatch<'data>) -> MatchResult+'data>(
    &self,
    data: &'data [&'data [c_char]],
    flags: ScanFlags,
    scratch: &mut Scratch,
    mut f: F,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, HyperscanError>>+'data {
    /* NB: while static arrays take up no extra runtime space, a ref to a slice
     * takes up more than pointer space! */
    static_assertions::assert_eq_size!([u8; 4], u32);
    static_assertions::assert_eq_size!(&u8, *const u8);
    static_assertions::const_assert_ne!(mem::size_of::<&[u8]>(), mem::size_of::<*const u8>());
    let data_len: usize = data.len();
    let lengths: Vec<c_uint> = data.iter().map(|col| col.len() as c_uint).collect();
    let data_pointers: Vec<*const c_char> = data.iter().map(|col| col.as_ptr()).collect();

    let f: &'static mut u8 = unsafe { mem::transmute(&mut f) };
    let mut matcher = VectoredSliceMatcher::new::<F>(data, unsafe { mem::transmute(f) });

    let s: &hs::hs_database = self.as_ref();
    let s: usize = unsafe { mem::transmute(s) };
    let data: *const *const c_char = data_pointers.as_ptr();
    let data: usize = unsafe { mem::transmute(data) };
    let scratch: &mut hs::hs_scratch = scratch.as_mut();
    let scratch: usize = unsafe { mem::transmute(scratch) };
    let ctx: usize = unsafe { mem::transmute(&mut matcher) };

    let scan_task = task::spawn_blocking(move || {
      HyperscanError::from_native(unsafe {
        hs::hs_scan_vector(
          s as *const hs::hs_database,
          data as *const *const c_char,
          lengths.as_ptr(),
          data_len as c_uint,
          flags.into_native(),
          scratch as *mut hs::hs_scratch,
          Some(match_slice_vectored_ref),
          ctx as *mut c_void,
        )
      })
    });

    try_stream! {
      let mut matcher = Pin::new(&mut matcher);
      while !scan_task.is_finished() {
        yield matcher.as_mut().await;
      }
      for m in matcher.pop_rest().into_iter() {
        yield m;
      }
      scan_task.await.unwrap()?;
    }
  }

  pub fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_database(self.as_mut()) })
  }
}

impl ops::Drop for Database {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

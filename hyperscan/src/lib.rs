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
#![feature(trait_alias)]

#[allow(unused, non_camel_case_types)]
mod bindings;

mod error;
pub use error::{CompileError, HyperscanCompileError, HyperscanError, HyperscanFlagsError};

mod flags;
pub use flags::{CpuFeatures, Flags, Mode, TuneFamily};

pub(crate) use bindings as hs;

use async_stream::try_stream;
use displaydoc::Display;
use futures_core::stream::Stream;
use once_cell::sync::Lazy;
use tokio::task;

use std::{
  ffi::CStr,
  mem, ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
};

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct Platform(pub hs::hs_platform_info);

static CACHED_PLATFORM: Lazy<Platform> = Lazy::new(|| Platform::populate().unwrap());

impl Platform {
  #[inline]
  pub fn tune(&self) -> TuneFamily { TuneFamily::from_native(self.0.tune) }

  #[inline]
  pub fn set_tune(&mut self, tune: TuneFamily) { self.0.tune = tune.into_native(); }

  #[inline]
  pub fn cpu_features(&self) -> CpuFeatures { CpuFeatures::from_native(self.0.cpu_features) }

  #[inline]
  pub fn set_cpu_features(&mut self, cpu_features: CpuFeatures) {
    self.0.cpu_features = cpu_features.into_native();
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
struct MatchEvent {
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

  #[inline(always)]
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

pub type VectoredByteSlices<'a> = &'a [ByteSlice<'a>];

mod matchers;
use matchers::{
  contiguous_slice::{match_slice_ref, SliceMatcher},
  vectored_slice::{match_slice_vectored_ref, VectoredSliceMatcher},
};
pub use matchers::{
  contiguous_slice::{Match, Scanner},
  vectored_slice::{VectorScanner, VectoredMatch},
};

#[derive(Debug)]
#[repr(transparent)]
pub struct Database(pub hs::hs_database);

impl AsRef<hs::hs_database> for Database {
  fn as_ref(&self) -> &hs::hs_database { &self.0 }
}

impl AsMut<hs::hs_database> for Database {
  fn as_mut(&mut self) -> &mut hs::hs_database { &mut self.0 }
}

impl Database {
  fn validate_flags_and_mode(
    flags: Flags,
    mode: Mode,
  ) -> Result<(c_uint, c_uint), HyperscanFlagsError> {
    mode.validate_db_type()?;
    mode.validate_against_flags(&flags)?;
    Ok((flags.into_native(), mode.into_native()))
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

  pub fn scan_matches<'data, F: Scanner<'data>>(
    &self,
    data: ByteSlice<'data>,
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

  pub fn scan_vector<'data, F: VectorScanner<'data>>(
    &self,
    data: VectoredByteSlices<'data>,
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

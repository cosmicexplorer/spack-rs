/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::HyperscanError,
  flags::{CpuFeatures, ScanFlags, TuneFamily},
  hs,
  matchers::{
    contiguous_slice::{match_slice_ref, Match, Scanner, SliceMatcher},
    vectored_slice::{
      match_slice_vectored_ref, VectorScanner, VectoredMatch, VectoredSliceMatcher,
    },
    ByteSlice, VectoredByteSlices,
  },
};

use futures_core::stream::Stream;
use once_cell::sync::Lazy;

use std::{cell, mem, ops, pin::Pin, ptr};

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct Platform(hs::hs_platform_info);

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
  fn populate() -> Result<Self, HyperscanError> {
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
pub struct Scratch<'db> {
  inner: *mut hs::hs_scratch,
  /* This ensures it's only ever used by the same database! */
  db: Pin<&'db Database>,
}

impl<'db> Scratch<'db> {
  pub fn alloc(db: Pin<&'db Database>) -> Result<Self, HyperscanError> {
    let mut scratch_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe {
      hs::hs_alloc_scratch(db.get_ref().as_ref(), &mut scratch_ptr)
    })?;
    Ok(Self {
      inner: scratch_ptr,
      db,
    })
  }

  pub fn get_size(&self) -> Result<usize, HyperscanError> {
    let mut n = mem::MaybeUninit::<usize>::uninit();
    HyperscanError::from_native(unsafe { hs::hs_scratch_size(self.as_ref(), n.as_mut_ptr()) })?;
    Ok(unsafe { n.assume_init() })
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanError> {
    let mut scratch_ptr = ptr::null_mut();
    HyperscanError::from_native(unsafe { hs::hs_clone_scratch(self.as_ref(), &mut scratch_ptr) })?;
    Ok(Self {
      inner: scratch_ptr,
      db: self.db,
    })
  }

  pub fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_scratch(self.as_mut()) })
  }

  pub fn scan<'data, F: Scanner<'data>>(
    &mut self,
    data: ByteSlice<'data>,
    flags: ScanFlags,
    f: F,
  ) -> impl Stream<Item=Result<Match<'data>, HyperscanError>>+'data {
    let s: &mut cell::UnsafeCell<Self> =
      unsafe { &mut *(self as *mut Self as *mut cell::UnsafeCell<Self>) };
    let db: Pin<&'db Database> = unsafe { &*s.get() }.db.as_ref();
    db.scan_matches(data, flags, unsafe { &mut *s.get() }, f)
  }
}

impl<'db> ops::Drop for Scratch<'db> {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

impl<'db> Clone for Scratch<'db> {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl<'db> AsRef<hs::hs_scratch> for Scratch<'db> {
  fn as_ref(&self) -> &hs::hs_scratch { unsafe { &*self.inner } }
}

impl<'db> AsMut<hs::hs_scratch> for Scratch<'db> {
  fn as_mut(&mut self) -> &mut hs::hs_scratch { unsafe { &mut *self.inner } }
}

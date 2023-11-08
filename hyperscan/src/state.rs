/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  error::HyperscanError,
  flags::{CpuFeatures, TuneFamily},
  hs, Database,
};

use once_cell::sync::Lazy;

use std::{mem, ops, pin::Pin};

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
#[repr(transparent)]
pub struct Scratch<'db> {
  inner: hs::hs_scratch,
  /* This ensures it's only ever used by the same database! */
  db: Pin<&'db Database>,
}

impl<'db> Scratch<'db> {
  pub fn alloc(db: Pin<&'db Database>) -> Result<Self, HyperscanError> {
    let mut scratch = mem::MaybeUninit::<hs::hs_scratch>::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_alloc_scratch(
        db.get_ref().as_ref(),
        mem::transmute(&mut scratch.as_mut_ptr()),
      )
    })?;
    Ok(Self {
      inner: unsafe { scratch.assume_init() },
      db,
    })
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
    Ok(Self {
      inner: unsafe { scratch.assume_init() },
      db: self.db,
    })
  }

  pub fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_scratch(self.as_mut()) })
  }
}

impl<'db> ops::Drop for Scratch<'db> {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

impl<'db> Clone for Scratch<'db> {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl<'db> AsRef<hs::hs_scratch> for Scratch<'db> {
  fn as_ref(&self) -> &hs::hs_scratch { &self.inner }
}

impl<'db> AsMut<hs::hs_scratch> for Scratch<'db> {
  fn as_mut(&mut self) -> &mut hs::hs_scratch { &mut self.inner }
}

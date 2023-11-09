/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::HyperscanError,
  flags::{CpuFeatures, ScanFlags, TuneFamily},
  hs,
  matchers::{
    contiguous_slice::{Match, Scanner},
    vectored_slice::{VectorScanner, VectoredMatch},
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

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*, state::*};
  /// use futures_util::TryStreamExt;
  /// use std::pin::Pin;
  ///
  /// let a_expr = Expression::new("a+")?;
  /// let b_expr = Expression::new("b+")?;
  /// let expr_set = ExpressionSet::from_exprs(&[&a_expr, &b_expr])
  ///   .with_flags(&[Flags::UTF8, Flags::UTF8])
  ///   .with_ids(&[ExprId(1), ExprId(2)]);
  ///
  /// let db = Database::compile_multi(&expr_set, Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::alloc(Pin::new(&db))?;
  /// let mut scratch = Pin::new(&mut scratch);
  ///
  /// let scan_flags = ScanFlags::default();
  ///
  /// let matches: Vec<&str> = scratch
  ///   .as_mut()
  ///   .scan(b"aardvark".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.decode_utf8().unwrap()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "aardva"]);
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(b"imbibe".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.decode_utf8().unwrap()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["imb", "imbib"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan<'data, F: Scanner<'data>>(
    self: Pin<&mut Self>,
    data: ByteSlice<'data>,
    flags: ScanFlags,
    f: F,
  ) -> impl Stream<Item=Result<Match<'data>, HyperscanError>>+'data {
    let s: &mut cell::UnsafeCell<Self> =
      unsafe { &mut *(self.get_mut() as *mut Self as *mut cell::UnsafeCell<Self>) };
    let db: Pin<&'db Database> = unsafe { &*s.get() }.db.as_ref();
    let scratch: Pin<&mut Self> = Pin::new(unsafe { &mut *s.get() });
    db.scan_matches(data, flags, scratch, f)
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*, state::*};
  /// use futures_util::TryStreamExt;
  /// use std::pin::Pin;
  ///
  /// let a_plus = Expression::new("a+")?;
  /// let b_plus = Expression::new("b+")?;
  /// let asdf = Expression::new("asdf")?;
  /// let expr_set = ExpressionSet::from_exprs(&[
  ///   &a_plus,
  ///   &b_plus,
  ///   &asdf,
  /// ])
  ///   .with_flags(&[Flags::UTF8, Flags::UTF8, Flags::UTF8])
  ///   .with_ids(&[ExprId(1), ExprId(2), ExprId(3)]);
  ///
  /// let db = Database::compile_multi(&expr_set, Mode::VECTORED)?;
  ///
  /// let mut scratch = Scratch::alloc(Pin::new(&db))?;
  /// let scratch = Pin::new(&mut scratch);
  ///
  /// let scan_flags = ScanFlags::default();
  /// let slices = vec![
  ///   b"aardvark".into(),
  ///   b"imbibe".into(),
  ///   b"leas".into(),
  ///   b"dfeg".into(),
  /// ];
  /// let data = VectoredByteSlices(slices.as_ref());
  /// let matches: Vec<Vec<&str>> = scratch
  ///   .scan_vectored(data, scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.into_iter().map(|s| s.decode_utf8().unwrap()).collect()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &[vec!["a"], vec!["aa"], vec!["aardva"]]);
  /// assert_eq!(&matches, &[vec!["imb"], vec!["imbib"]]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan_vectored<'data, F: VectorScanner<'data>>(
    self: Pin<&mut Self>,
    data: VectoredByteSlices<'data>,
    flags: ScanFlags,
    f: F,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, HyperscanError>>+'data {
    let s: &mut cell::UnsafeCell<Self> =
      unsafe { &mut *(self.get_mut() as *mut Self as *mut cell::UnsafeCell<Self>) };
    let db: Pin<&'db Database> = unsafe { &*s.get() }.db.as_ref();
    let scratch: Pin<&mut Self> = Pin::new(unsafe { &mut *s.get() });
    db.scan_vector(data, flags, scratch, f)
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

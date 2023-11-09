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

use async_stream::try_stream;
use futures_core::stream::Stream;
use once_cell::sync::Lazy;
use tokio::task;

use std::{mem, ops, pin::Pin, ptr};

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
  pub fn pinned_db(self: Pin<&Self>) -> Pin<&'db Database> { self.db }

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

  fn try_drop(self: Pin<&mut Self>) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_scratch(self.get_mut().as_mut()) })
  }

  fn db_ptr(&self) -> *const hs::hs_database {
    let db: &Database = &self.db.as_ref();
    db.as_ref()
  }

  fn into_slice_ctx(m: SliceMatcher) -> usize {
    let ctx: *mut SliceMatcher = Box::into_raw(Box::new(m));
    ctx as usize
  }

  fn from_slice_ctx<'data, 'code>(ctx: usize) -> Pin<Box<SliceMatcher<'data, 'code>>> {
    Box::into_pin(unsafe { Box::from_raw(ctx as *mut SliceMatcher) })
  }

  fn into_vectored_ctx(m: VectoredSliceMatcher) -> usize {
    let ctx: *mut VectoredSliceMatcher = Box::into_raw(Box::new(m));
    ctx as usize
  }

  fn from_vectored_ctx<'data, 'code>(ctx: usize) -> Pin<Box<VectoredSliceMatcher<'data, 'code>>> {
    Box::into_pin(unsafe { Box::from_raw(ctx as *mut VectoredSliceMatcher) })
  }

  fn into_scratch(scratch: Pin<&mut Scratch>) -> usize {
    let scratch: *mut Scratch = scratch.get_mut();
    scratch as usize
  }

  fn from_scratch<'a>(scratch: usize) -> Pin<&'a mut Scratch<'a>> {
    Pin::new(unsafe { &mut *(scratch as *mut Scratch) })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*, state::*, error::*};
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
  ///   .as_mut()
  ///   .scan(b"imbibe".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.decode_utf8().unwrap()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["imb", "imbib"]);
  ///
  /// let ret = scratch
  ///   .scan(b"abwuebiaubeb".into(), scan_flags, |_| MatchResult::CeaseMatching)
  ///   .try_for_each(|_| async { Ok(()) })
  ///   .await;
  /// assert!(matches![ret, Err(HyperscanError::ScanTerminated)]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan<'data, F: Scanner<'data>>(
    self: Pin<&mut Self>,
    data: ByteSlice<'data>,
    flags: ScanFlags,
    mut f: F,
  ) -> impl Stream<Item=Result<Match<'data>, HyperscanError>>+'data {
    let (matcher, mut matches_rx) = SliceMatcher::new::<32, _>(data, &mut f);

    let ctx = Self::into_slice_ctx(matcher);
    let scratch = Self::into_scratch(self);

    let scan_task = task::spawn_blocking(move || {
      let scratch: Pin<&mut Scratch> = Self::from_scratch(scratch);
      let mut matcher: Pin<Box<SliceMatcher>> = Self::from_slice_ctx(ctx);
      let parent_slice = matcher.parent_slice();
      HyperscanError::from_native(unsafe {
        hs::hs_scan(
          scratch.db_ptr(),
          parent_slice.as_ptr(),
          parent_slice.native_len(),
          flags.into_native(),
          scratch.get_mut().as_mut(),
          Some(match_slice_ref),
          mem::transmute(matcher.as_mut().get_mut()),
        )
      })
    });

    try_stream! {
      while let Some(m) = matches_rx.recv().await {
        yield m;
      }
      scan_task.await.unwrap()?;
    }
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
  /// assert_eq!(&matches, &[
  ///   vec!["a"], vec!["aa"], vec!["aardva"],
  ///   vec!["aardvark", "imb"], vec!["aardvark", "imbib"],
  ///   vec!["aardvark", "imbibe", "lea"],
  ///   vec!["aardvark", "imbibe", "leas", "df"],
  /// ]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan_vectored<'data, F: VectorScanner<'data>>(
    self: Pin<&mut Self>,
    data: VectoredByteSlices<'data>,
    flags: ScanFlags,
    mut f: F,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, HyperscanError>>+'data {
    /* NB: while static arrays take up no extra runtime space, a ref to a
    slice
    * takes up more than pointer space! */
    static_assertions::assert_eq_size!([u8; 4], u32);
    static_assertions::assert_eq_size!(&u8, *const u8);
    static_assertions::const_assert_ne!(mem::size_of::<&[u8]>(), mem::size_of::<*const u8>());

    let (matcher, mut matches_rx) = VectoredSliceMatcher::new::<32, _>(data, &mut f);

    let ctx = Self::into_vectored_ctx(matcher);
    let scratch = Self::into_scratch(self);

    let scan_task = task::spawn_blocking(move || {
      let scratch: Pin<&mut Scratch> = Self::from_scratch(scratch);
      let mut matcher: Pin<Box<VectoredSliceMatcher>> = Self::from_vectored_ctx(ctx);
      let parent_slices = matcher.parent_slices();
      let (data_pointers, lengths) = parent_slices.pointers_and_lengths();
      HyperscanError::from_native(unsafe {
        hs::hs_scan_vector(
          scratch.db_ptr(),
          data_pointers.as_ptr(),
          lengths.as_ptr(),
          parent_slices.native_len(),
          flags.into_native(),
          scratch.get_mut().as_mut(),
          Some(match_slice_vectored_ref),
          mem::transmute(matcher.as_mut().get_mut()),
        )
      })
    });

    try_stream! {
      while let Some(m) = matches_rx.recv().await {
        yield m;
      }
      scan_task.await.unwrap()?;
    }
  }
}

impl<'db> ops::Drop for Scratch<'db> {
  fn drop(&mut self) { Pin::new(self).try_drop().unwrap(); }
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

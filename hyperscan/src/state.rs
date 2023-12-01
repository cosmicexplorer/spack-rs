/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::HyperscanError,
  flags::{CpuFeatures, ScanFlags, TuneFamily},
  hs,
  matchers::{
    contiguous_slice::{match_slice_ref, Match, SliceMatcher},
    vectored_slice::{match_slice_vectored_ref, VectoredMatch, VectoredSliceMatcher},
    ByteSlice, MatchResult, VectoredByteSlices,
  },
};

use async_stream::try_stream;
use futures_core::stream::Stream;
use once_cell::sync::Lazy;
use tokio::task;

use std::{
  mem, ops,
  pin::Pin,
  ptr::{self, NonNull},
};

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
  pub fn get() -> &'static Self { &CACHED_PLATFORM }

  #[inline]
  pub(crate) fn as_ref_native(&self) -> &hs::hs_platform_info { &self.0 }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Scratch(Option<NonNull<hs::hs_scratch>>);

impl Scratch {
  #[inline]
  pub const fn new() -> Self { Self(None) }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, matchers::*, state::*};
  /// use futures_util::TryStreamExt;
  ///
  /// let a_expr: Expression = "a+".parse()?;
  /// let a_db = a_expr.compile(Flags::UTF8 | Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  /// let b_expr: Expression = "b+".parse()?;
  /// let b_db = b_expr.compile(Flags::UTF8 | Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::new();
  /// scratch.setup_for_db(&a_db)?;
  /// scratch.setup_for_db(&b_db)?;
  ///
  /// let scan_flags = ScanFlags::default();
  /// let s: ByteSlice = "ababaabb".into();
  /// let matches: Vec<&str> = scratch
  ///   .scan(&a_db, s, scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "a", "a", "aa"]);
  /// let matches: Vec<&str> = scratch
  ///   .scan(&b_db, s, scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["b", "b", "b", "bb"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn setup_for_db(&mut self, db: &Database) -> Result<(), HyperscanError> {
    let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
    HyperscanError::from_native(unsafe {
      hs::hs_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
    })?;
    self.0 = NonNull::new(scratch_ptr);
    Ok(())
  }

  #[inline]
  pub(crate) fn as_ref_native(&self) -> Option<&hs::hs_scratch> {
    self.0.map(|p| unsafe { p.as_ref() })
  }

  #[inline]
  pub(crate) fn as_mut_native(&mut self) -> Option<&mut hs::hs_scratch> {
    self.0.map(|mut p| unsafe { p.as_mut() })
  }

  pub fn get_size(&self) -> Result<usize, HyperscanError> {
    match self.as_ref_native() {
      None => Ok(0),
      Some(p) => {
        let mut n = mem::MaybeUninit::<usize>::uninit();
        HyperscanError::from_native(unsafe { hs::hs_scratch_size(p, n.as_mut_ptr()) })?;
        Ok(unsafe { n.assume_init() })
      },
    }
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

  fn into_db(db: &Database) -> usize {
    let db: *const Database = db;
    db as usize
  }

  fn from_db<'a>(db: usize) -> &'a Database { unsafe { &*(db as *const Database) } }

  fn into_scratch(scratch: &mut Scratch) -> usize {
    let scratch: *mut Scratch = scratch;
    scratch as usize
  }

  fn from_scratch<'a>(scratch: usize) -> &'a mut Scratch {
    unsafe { &mut *(scratch as *mut Scratch) }
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, error::*};
  /// use futures_util::TryStreamExt;
  ///
  /// let a_expr: Expression = "a+".parse()?;
  /// let b_expr: Expression = "b+".parse()?;
  /// let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  /// let expr_set = ExpressionSet::from_exprs(&[&a_expr, &b_expr])
  ///   .with_flags(&[flags, flags])
  ///   .with_ids(&[ExprId(1), ExprId(2)]);
  /// let db = expr_set.compile(Mode::BLOCK)?;
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let scan_flags = ScanFlags::default();
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "aardvark".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|Match { source, .. }| async move { Ok(source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "a"]);
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "imbibbe".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|Match { source, .. }| async move { Ok(source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["b", "b", "bb"]);
  ///
  /// let ret = scratch
  ///   .scan(&db, "abwuebiaubeb".into(), scan_flags, |_| MatchResult::CeaseMatching)
  ///   .try_for_each(|_| async { Ok(()) })
  ///   .await;
  /// assert!(matches![ret, Err(HyperscanError::ScanTerminated)]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan<'data, F: FnMut(&Match<'data>) -> MatchResult+'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    flags: ScanFlags,
    mut f: F,
  ) -> impl Stream<Item=Result<Match<'data>, HyperscanError>>+'data {
    let (matcher, mut matches_rx) = SliceMatcher::new(data, &mut f);

    let ctx = Self::into_slice_ctx(matcher);
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);

    let scan_task = task::spawn_blocking(move || {
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);
      let mut matcher: Pin<Box<SliceMatcher>> = Self::from_slice_ctx(ctx);
      let parent_slice = matcher.parent_slice();
      HyperscanError::from_native(unsafe {
        hs::hs_scan(
          db.as_ref_native(),
          parent_slice.as_ptr(),
          parent_slice.native_len(),
          flags.into_native(),
          scratch.as_mut_native().unwrap(),
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
  /// use hyperscan::{expression::*, flags::*, matchers::{*, vectored_slice::*}};
  /// use futures_util::TryStreamExt;
  ///
  /// let a_plus: Expression = "a+".parse()?;
  /// let b_plus: Expression = "b+".parse()?;
  /// let asdf: Expression = "asdf(.)".parse()?;
  /// let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  /// let expr_set = ExpressionSet::from_exprs(&[&a_plus, &b_plus, &asdf])
  ///   .with_flags(&[flags, flags, flags])
  ///   .with_ids(&[ExprId(0), ExprId(3), ExprId(2)]);
  /// let db = expr_set.compile(Mode::VECTORED)?;
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let data: [ByteSlice; 4] = [
  ///   "aardvark".into(),
  ///   "imbibbe".into(),
  ///   "leas".into(),
  ///   "dfeg".into(),
  /// ];
  /// let matches: Vec<(u32, String)> = scratch
  ///   .scan_vectored(&db, data.as_ref().into(), ScanFlags::default(), |_| MatchResult::Continue)
  ///   .and_then(|VectoredMatch { id: ExpressionIndex(id), source, .. }| async move {
  ///     let joined = source.into_iter().map(|s| s.as_str()).collect::<Vec<_>>().concat();
  ///     Ok((id, joined))
  ///   })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(matches, vec![
  ///   (0, "a".to_string()),
  ///   (0, "aa".to_string()),
  ///   (0, "a".to_string()),
  ///   (3, "b".to_string()),
  ///   (3, "b".to_string()),
  ///   (3, "bb".to_string()),
  ///   (0, "a".to_string()),
  ///   (2, "asdfe".to_string()),
  /// ]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan_vectored<'data, F: FnMut(&VectoredMatch<'data>) -> MatchResult+'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data>,
    flags: ScanFlags,
    mut f: F,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, HyperscanError>>+'data {
    /* NB: while static arrays take up no extra runtime space, a ref to a
    slice
    * takes up more than pointer space! */
    static_assertions::assert_eq_size!([u8; 4], u32);
    static_assertions::assert_eq_size!(&u8, *const u8);
    static_assertions::assert_eq_size!(&[u8; 4], *const u8);
    static_assertions::const_assert!(mem::size_of::<&[u8]>() > mem::size_of::<*const u8>());

    let (matcher, mut matches_rx) = VectoredSliceMatcher::new(data, &mut f);

    let ctx = Self::into_vectored_ctx(matcher);
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);

    let scan_task = task::spawn_blocking(move || {
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);
      let mut matcher: Pin<Box<VectoredSliceMatcher>> = Self::from_vectored_ctx(ctx);
      let parent_slices = matcher.parent_slices();
      let (data_pointers, lengths) = parent_slices.pointers_and_lengths();
      HyperscanError::from_native(unsafe {
        hs::hs_scan_vector(
          db.as_ref_native(),
          data_pointers.as_ptr(),
          lengths.as_ptr(),
          parent_slices.native_len(),
          flags.into_native(),
          scratch.as_mut_native().unwrap(),
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

  pub fn try_clone(&self) -> Result<Self, HyperscanError> {
    match self.as_ref_native() {
      None => Ok(Self::new()),
      Some(p) => {
        let mut scratch_ptr = ptr::null_mut();
        HyperscanError::from_native(unsafe { hs::hs_clone_scratch(p, &mut scratch_ptr) })?;
        Ok(Self(NonNull::new(scratch_ptr)))
      },
    }
  }

  pub unsafe fn try_drop(&mut self) -> Result<(), HyperscanError> {
    if let Some(p) = self.as_mut_native() {
      HyperscanError::from_native(unsafe { hs::hs_free_scratch(p) })?;
    }
    Ok(())
  }
}

impl Clone for Scratch {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl ops::Drop for Scratch {
  fn drop(&mut self) {
    unsafe {
      self.try_drop().unwrap();
    }
  }
}

unsafe impl Send for Scratch {}
unsafe impl Sync for Scratch {}

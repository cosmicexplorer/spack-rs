/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  database::Database,
  error::{HyperscanRuntimeError, ScanError},
  hs,
  matchers::{
    contiguous_slice::{match_slice_ref_sync, Match, SyncSliceMatcher},
    vectored_slice::{match_slice_vectored_ref_sync, SyncVectoredSliceMatcher, VectoredMatch},
    ByteSlice, MatchResult, VectoredByteSlices,
  },
};

use async_stream::try_stream;
use futures_core::stream::Stream;
use tokio::{sync::mpsc, task};

use std::{
  mem, ops,
  ptr::{self, NonNull},
};

pub type NativeScratch = hs::hs_scratch;

#[derive(Debug)]
#[repr(transparent)]
pub struct Scratch(Option<NonNull<NativeScratch>>);

impl Scratch {
  pub const fn new() -> Self { Self(None) }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
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
  /// let s: ByteSlice = "ababaabb".into();
  /// let matches: Vec<&str> = scratch
  ///   .scan(&a_db, s, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "a", "a", "aa"]);
  /// let matches: Vec<&str> = scratch
  ///   .scan(&b_db, s, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["b", "b", "b", "bb"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn setup_for_db(&mut self, db: &Database) -> Result<(), HyperscanRuntimeError> {
    let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
    })?;
    self.0 = NonNull::new(scratch_ptr);
    Ok(())
  }

  pub fn as_ref_native(&self) -> Option<&NativeScratch> { self.0.map(|p| unsafe { p.as_ref() }) }

  pub fn as_mut_native(&mut self) -> Option<&mut NativeScratch> {
    self.0.map(|mut p| unsafe { p.as_mut() })
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
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, error::*};
  ///
  /// let a_expr: Expression = "a+".parse()?;
  /// let b_expr: Expression = "b+".parse()?;
  /// let flags = Flags::SOM_LEFTMOST;
  /// let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///   .with_flags([flags, flags])
  ///   .with_ids([ExprId(1), ExprId(2)]);
  /// let db = expr_set.compile(Mode::BLOCK)?;
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// {
  ///   let mut f = |Match { source, .. }| {
  ///     matches.push(unsafe { source.as_str() });
  ///     MatchResult::Continue
  ///   };
  ///   scratch.scan_sync(&db, "aardvark".into(), &mut f)?;
  ///   scratch.scan_sync(&db, "imbibbe".into(), &mut f)?;
  /// }
  /// assert_eq!(&matches, &["a", "aa", "a", "b", "b", "bb"]);
  ///
  /// let ret = scratch.scan_sync(&db, "abwuebiaubeb".into(), |_| MatchResult::CeaseMatching);
  /// assert!(matches![ret, Err(HyperscanRuntimeError::ScanTerminated)]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn scan_sync<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    mut f: impl FnMut(Match<'data>) -> MatchResult,
  ) -> Result<(), HyperscanRuntimeError> {
    let mut matcher = SyncSliceMatcher::new(data, &mut f);
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan(
        db.as_ref_native(),
        matcher.parent_slice().as_ptr(),
        matcher.parent_slice().native_len(),
        /* NB: ignoring flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice_ref_sync),
        mem::transmute(&mut matcher),
      )
    })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, error::*};
  /// use futures_util::TryStreamExt;
  ///
  /// let a_expr: Expression = "a+".parse()?;
  /// let b_expr: Expression = "b+".parse()?;
  /// let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  /// let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///   .with_flags([flags, flags])
  ///   .with_ids([ExprId(1), ExprId(2)]);
  /// let db = expr_set.compile(Mode::BLOCK)?;
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "aardvark".into(), |_| MatchResult::Continue)
  ///   .and_then(|Match { source, .. }| async move { Ok(unsafe { source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "a"]);
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "imbibbe".into(), |_| MatchResult::Continue)
  ///   .and_then(|Match { source, .. }| async move { Ok(unsafe { source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["b", "b", "bb"]);
  ///
  /// let ret = scratch
  ///   .scan(&db, "abwuebiaubeb".into(), |_| MatchResult::CeaseMatching)
  ///   .try_for_each(|_| async { Ok(()) })
  ///   .await;
  /// assert!(matches![ret, Err(ScanError::ReturnValue(HyperscanRuntimeError::ScanTerminated))]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn scan<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    mut f: impl FnMut(&Match<'data>) -> MatchResult+Send+Sync,
  ) -> impl Stream<Item=Result<Match<'data>, ScanError>> {
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);
    let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
    let f: &mut (dyn FnMut(&Match<'data>) -> MatchResult+Send+Sync) = &mut f;
    let (matches_tx, mut matches_rx) = mpsc::unbounded_channel();

    let f: &'static mut (dyn FnMut(&Match<'static>) -> MatchResult+Send+Sync) =
      unsafe { mem::transmute(f) };
    let matches_tx: mpsc::UnboundedSender<Match<'static>> = unsafe { mem::transmute(matches_tx) };
    let scan_task = task::spawn_blocking(move || {
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);
      scratch.scan_sync(db, data, |m| {
        let result = f(&m);
        matches_tx.send(m).unwrap();
        result
      })
    });

    try_stream! {
      while let Some(m) = matches_rx.recv().await {
        yield m;
      }
      scan_task.await??;
    }
  }

  pub fn scan_vectored_sync<'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data>,
    mut f: impl FnMut(VectoredMatch<'data>) -> MatchResult,
  ) -> Result<(), HyperscanRuntimeError> {
    let mut matcher = SyncVectoredSliceMatcher::new(data, &mut f);
    let (data_pointers, lengths) = matcher.parent_slices().pointers_and_lengths();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan_vector(
        db.as_ref_native(),
        data_pointers.as_ptr(),
        lengths.as_ptr(),
        matcher.parent_slices().native_len(),
        /* NB: ignoring flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice_vectored_ref_sync),
        mem::transmute(&mut matcher),
      )
    })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, matchers::{*, vectored_slice::*}};
  /// use futures_util::TryStreamExt;
  ///
  /// let a_plus: Expression = "a+".parse()?;
  /// let b_plus: Expression = "b+".parse()?;
  /// let asdf: Expression = "asdf(.)".parse()?;
  /// let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  /// let expr_set = ExpressionSet::from_exprs([&a_plus, &b_plus, &asdf])
  ///   .with_flags([flags, flags, flags])
  ///   .with_ids([ExprId(0), ExprId(3), ExprId(2)]);
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
  ///   .scan_vectored(&db, data.as_ref().into(), |_| MatchResult::Continue)
  ///   .and_then(|VectoredMatch { id: ExpressionIndex(id), source, .. }| async move {
  ///     let joined = source.into_iter()
  ///       .map(|s| unsafe { s.as_str() })
  ///       .collect::<Vec<_>>()
  ///       .concat();
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
  pub fn scan_vectored<'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data>,
    mut f: impl FnMut(&VectoredMatch<'data>) -> MatchResult+Send+Sync,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, ScanError>> {
    /* NB: while static arrays take up no extra runtime space, a ref to a
    slice
    * takes up more than pointer space! */
    static_assertions::assert_eq_size!([u8; 4], u32);
    static_assertions::assert_eq_size!(&u8, *const u8);
    static_assertions::assert_eq_size!(&[u8; 4], *const u8);
    static_assertions::const_assert!(mem::size_of::<&[u8]>() > mem::size_of::<*const u8>());

    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);
    let data: VectoredByteSlices<'static> = unsafe { mem::transmute(data) };
    let f: &mut (dyn FnMut(&VectoredMatch<'data>) -> MatchResult+Send+Sync) = &mut f;
    let (matches_tx, mut matches_rx) = mpsc::unbounded_channel();

    let f: &'static mut (dyn FnMut(&VectoredMatch<'static>) -> MatchResult+Send+Sync) =
      unsafe { mem::transmute(f) };
    let matches_tx: mpsc::UnboundedSender<VectoredMatch<'static>> =
      unsafe { mem::transmute(matches_tx) };
    let scan_task = task::spawn_blocking(move || {
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);
      scratch.scan_vectored_sync(db, data, |m| {
        let result = f(&m);
        matches_tx.send(m).unwrap();
        result
      })
    });

    try_stream! {
      while let Some(m) = matches_rx.recv().await {
        yield m;
      }
      scan_task.await??;
    }
  }

  pub fn get_size(&self) -> Result<usize, HyperscanRuntimeError> {
    match self.as_ref_native() {
      None => Ok(0),
      Some(p) => {
        let mut n = mem::MaybeUninit::<usize>::uninit();
        HyperscanRuntimeError::from_native(unsafe { hs::hs_scratch_size(p, n.as_mut_ptr()) })?;
        Ok(unsafe { n.assume_init() })
      },
    }
  }

  pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
    match self.as_ref_native() {
      None => Ok(Self::new()),
      Some(p) => {
        let mut scratch_ptr = ptr::null_mut();
        HyperscanRuntimeError::from_native(unsafe { hs::hs_clone_scratch(p, &mut scratch_ptr) })?;
        Ok(Self(NonNull::new(scratch_ptr)))
      },
    }
  }

  pub unsafe fn try_drop(&mut self) -> Result<(), HyperscanRuntimeError> {
    if let Some(p) = self.as_mut_native() {
      HyperscanRuntimeError::from_native(unsafe { hs::hs_free_scratch(p) })?;
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

#[cfg(all(test, feature = "compile"))]
mod test {
  use crate::{
    expression::Expression,
    flags::{Flags, Mode},
    matchers::MatchResult,
  };

  use futures_util::TryStreamExt;

  use std::{mem::ManuallyDrop, sync::Arc};

  #[tokio::test]
  async fn try_clone_still_valid() -> Result<(), eyre::Report> {
    let a_expr: Expression = "asdf$".parse()?;
    let db = a_expr.compile(Flags::UTF8, Mode::BLOCK)?;

    /* Allocate a new scratch. */
    let mut scratch = ManuallyDrop::new(db.allocate_scratch()?);
    /* Clone it. */
    let mut s2 = ManuallyDrop::new(scratch.try_clone()?);
    /* Drop the first scratch. */
    unsafe {
      scratch.try_drop()?;
    }

    /* Operate on the clone. */
    let matches: Vec<&str> = s2
      .scan(&db, "asdf".into(), |_| MatchResult::Continue)
      .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
      .try_collect()
      .await?;

    assert_eq!(&matches, &["asdf"]);

    unsafe {
      s2.try_drop()?;
    }

    Ok(())
  }

  #[tokio::test]
  async fn make_mut() -> Result<(), eyre::Report> {
    let a_expr: Expression = "asdf$".parse()?;
    let db = a_expr.compile(Flags::UTF8, Mode::BLOCK)?;

    /* Allocate a new scratch into an Arc. */
    let scratch = Arc::new(db.allocate_scratch()?);
    /* Clone the Arc. */
    let mut s2 = Arc::clone(&scratch);

    /* Operate on the result of Arc::make_mut(). */
    let matches: Vec<&str> = Arc::make_mut(&mut s2)
      .scan(&db, "asdf".into(), |_| MatchResult::Continue)
      .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
      .try_collect()
      .await?;

    assert_eq!(&matches, &["asdf"]);
    Ok(())
  }
}

#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;
  use crate::{database::chimera::ChimeraDb, error::chimera::*, matchers::chimera::*};

  use async_stream::stream;

  pub type NativeChimeraScratch = hs::ch_scratch;

  #[derive(Debug)]
  #[repr(transparent)]
  pub struct ChimeraScratch(Option<NonNull<NativeChimeraScratch>>);

  impl ChimeraScratch {
    pub const fn new() -> Self { Self(None) }

    pub fn setup_for_db(&mut self, db: &ChimeraDb) -> Result<(), ChimeraRuntimeError> {
      let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
      })?;
      self.0 = NonNull::new(scratch_ptr);
      Ok(())
    }

    pub fn as_ref_native(&self) -> Option<&NativeChimeraScratch> {
      self.0.map(|p| unsafe { p.as_ref() })
    }

    pub fn as_mut_native(&mut self) -> Option<&mut NativeChimeraScratch> {
      self.0.map(|mut p| unsafe { p.as_mut() })
    }

    fn into_db(db: &ChimeraDb) -> usize {
      let db: *const ChimeraDb = db;
      db as usize
    }

    fn from_db<'a>(db: usize) -> &'a ChimeraDb { unsafe { &*(db as *const ChimeraDb) } }

    fn into_scratch(scratch: &mut ChimeraScratch) -> usize {
      let scratch: *mut ChimeraScratch = scratch;
      scratch as usize
    }

    fn from_scratch<'a>(scratch: usize) -> &'a mut ChimeraScratch {
      unsafe { &mut *(scratch as *mut ChimeraScratch) }
    }

    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*};
    ///
    /// let expr: ChimeraExpression = "a+(.)".parse()?;
    /// let db = expr.compile(ChimeraFlags::UTF8, ChimeraMode::GROUPS)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let mut matches: Vec<(&str, &str)> = Vec::new();
    /// scratch.scan_sync(
    ///   &db,
    ///   "aardvark".into(),
    ///   |ChimeraMatch { source, captures, .. }| {
    ///     matches.push(unsafe { (source.as_str(), captures[1].unwrap().as_str()) });
    ///     ChimeraMatchResult::Continue
    ///   },
    ///   |_| ChimeraMatchResult::Continue,
    ///  )?;
    /// assert_eq!(&matches, &[("aar", "r"), ("ar", "r")]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn scan_sync<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
      mut m: impl FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult,
      mut e: impl FnMut(ChimeraMatchError) -> ChimeraMatchResult,
    ) -> Result<(), ChimeraRuntimeError> {
      let mut matcher = ChimeraSyncSliceMatcher::new(data, &mut m, &mut e);
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_scan(
          db.as_ref_native(),
          matcher.parent_slice().as_ptr(),
          matcher.parent_slice().native_len(),
          /* NB: ignoring flags for now! */
          0,
          self.as_mut_native().unwrap(),
          Some(match_chimera_slice_sync),
          Some(error_callback_chimera_sync),
          mem::transmute(&mut matcher),
        )
      })
    }

    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// # tokio_test::block_on(async {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, error::chimera::*};
    /// use futures_util::TryStreamExt;
    ///
    /// let expr: ChimeraExpression = "a+(.)".parse()?;
    /// let db = expr.compile(ChimeraFlags::UTF8, ChimeraMode::GROUPS)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let m = |_: &ChimeraMatch| ChimeraMatchResult::Continue;
    /// let e = |_: &ChimeraMatchError| ChimeraMatchResult::Continue;
    /// let matches: Vec<(&str, &str)> = scratch.scan(&db, "aardvark".into(), m, e)
    ///  .and_then(|ChimeraMatch { source, captures, .. }| async move {
    ///    Ok(unsafe { (source.as_str(), captures[1].unwrap().as_str()) })
    ///  })
    ///  .try_collect()
    ///  .await?;
    /// assert_eq!(&matches, &[("aar", "r"), ("ar", "r")]);
    /// # Ok(())
    /// # })}
    /// ```
    pub fn scan<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
      mut m: impl FnMut(&ChimeraMatch<'data>) -> ChimeraMatchResult+Send+Sync,
      mut e: impl FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync,
    ) -> impl Stream<Item=Result<ChimeraMatch<'data>, ChimeraScanError>> {
      let scratch = Self::into_scratch(self);
      let db = Self::into_db(db);
      let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
      let m: &mut (dyn FnMut(&ChimeraMatch<'data>) -> ChimeraMatchResult+Send+Sync) = &mut m;
      let e: &mut (dyn FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync) = &mut e;
      let (matches_tx, mut matches_rx) = mpsc::unbounded_channel();
      let (errors_tx, mut errors_rx) = mpsc::unbounded_channel();

      let m: &'static mut (dyn FnMut(&ChimeraMatch<'static>) -> ChimeraMatchResult+Send+Sync) =
        unsafe { mem::transmute(m) };
      let e: &'static mut (dyn FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync) =
        unsafe { mem::transmute(e) };
      let matches_tx: mpsc::UnboundedSender<ChimeraMatch<'static>> =
        unsafe { mem::transmute(matches_tx) };
      let scan_task = task::spawn_blocking(move || {
        let scratch: &mut Self = Self::from_scratch(scratch);
        let db: &ChimeraDb = Self::from_db(db);
        scratch.scan_sync(
          db,
          data,
          |cm| {
            let result = m(&cm);
            matches_tx.send(cm).unwrap();
            result
          },
          |ce| {
            let result = e(&ce);
            errors_tx.send(ce).unwrap();
            result
          },
        )
      });

      /* Need to use stream! instead of try_stream! in order to yield an Err inside
       * of a select! expression! */
      stream! {
        while tokio::select! {
          biased;
          Some(e) = errors_rx.recv() => { yield Err(e.into()); true },
          Some(m) = matches_rx.recv() => { yield Ok(m); true },
          else => false,
        } {}
        /* Propagate the error result of the scan task, or any internal panic that
         * occurred in the scan task, into an Err instance in the merged
         * Result stream. */
        match scan_task.await {
          Err(e) => {
            yield Err(e.into());
          },
          Ok(Err(e)) => {
            yield Err(e.into());
          },
          Ok(Ok(())) => (),
        }
      }
    }

    pub fn get_size(&self) -> Result<usize, ChimeraRuntimeError> {
      match self.as_ref_native() {
        None => Ok(0),
        Some(p) => {
          let mut n = mem::MaybeUninit::<usize>::uninit();
          ChimeraRuntimeError::from_native(unsafe { hs::ch_scratch_size(p, n.as_mut_ptr()) })?;
          Ok(unsafe { n.assume_init() })
        },
      }
    }

    pub fn try_clone(&self) -> Result<Self, ChimeraRuntimeError> {
      match self.as_ref_native() {
        None => Ok(Self::new()),
        Some(p) => {
          let mut scratch_ptr = ptr::null_mut();
          ChimeraRuntimeError::from_native(unsafe { hs::ch_clone_scratch(p, &mut scratch_ptr) })?;
          Ok(Self(NonNull::new(scratch_ptr)))
        },
      }
    }

    pub unsafe fn try_drop(&mut self) -> Result<(), ChimeraRuntimeError> {
      if let Some(p) = self.as_mut_native() {
        ChimeraRuntimeError::from_native(unsafe { hs::ch_free_scratch(p) })?;
      }
      Ok(())
    }
  }

  impl Clone for ChimeraScratch {
    fn clone(&self) -> Self { self.try_clone().unwrap() }
  }

  impl ops::Drop for ChimeraScratch {
    fn drop(&mut self) {
      unsafe {
        self.try_drop().unwrap();
      }
    }
  }
}

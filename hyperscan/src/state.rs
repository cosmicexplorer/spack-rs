/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  database::Database,
  error::HyperscanRuntimeError,
  hs,
  matchers::{
    contiguous_slice::{match_slice, Match, SliceMatcher},
    stream::match_slice_stream,
    vectored_slice::{match_slice_vectored, VectoredMatch, VectoredMatcher},
    MatchResult,
  },
  sources::{ByteSlice, VectoredByteSlices},
  stream::StreamSink,
};
#[cfg(feature = "async")]
use crate::{
  error::ScanError, matchers::stream::scan::scan_slice_stream, stream::channel::StreamSinkChannel,
};

#[cfg(feature = "async")]
use {
  futures_core::stream::Stream,
  tokio::{sync::mpsc, task},
};

use std::{
  mem, ops,
  ptr::{self, NonNull},
};

pub type NativeScratch = hs::hs_scratch;

#[derive(Debug)]
#[repr(transparent)]
pub struct Scratch(Option<NonNull<NativeScratch>>);

unsafe impl Send for Scratch {}
unsafe impl Sync for Scratch {}

/// # Setup Methods
/// These methods create a new scratch space or initialize it against a
/// database. [`Database::allocate_scratch()`] is also provided as a convenience
/// method to combine the creation and initialization steps.
impl Scratch {
  /// Return an uninitialized scratch space without allocation.
  pub const fn blank() -> Self { Self(None) }

  /// Initialize this scratch space against the given `db`.
  ///
  /// A single scratch space can be initialized against multiple databases, but
  /// exclusive mutable access is required to perform a search, so
  /// [`Self::try_clone()`] can be used to obtain multiple copies of a
  /// multiply-initialized scratch space.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, matchers::*, state::*, sources::*};
  ///
  ///   let a_expr: Expression = "a+".parse()?;
  ///   let a_db = a_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  ///   let b_expr: Expression = "b+".parse()?;
  ///   let b_db = b_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  ///   let mut scratch = Scratch::blank();
  ///   scratch.setup_for_db(&a_db)?;
  ///   scratch.setup_for_db(&b_db)?;
  ///
  ///   let s: ByteSlice = "ababaabb".into();
  ///
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch
  ///     .scan_sync(&a_db, s, |m| {
  ///       matches.push(unsafe { m.source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "a", "a", "aa"]);
  ///
  ///   matches.clear();
  ///   scratch
  ///     .scan_sync(&b_db, s, |m| {
  ///       matches.push(unsafe { m.source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["b", "b", "b", "bb"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn setup_for_db(&mut self, db: &Database) -> Result<(), HyperscanRuntimeError> {
    /* NB: this method always overwrites self.0, because `hs_alloc_scratch()` may
     * modify the pointer location if the scratch space needs to be resized! */
    let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
    })?;
    /* *self = unsafe { Self::from_native(scratch_ptr) }; */
    self.0 = NonNull::new(scratch_ptr);
    Ok(())
  }
}

/// # Synchronous String Scanning
/// Hyperscan's string search interface requires a C function pointer to call
/// synchronously upon each match. This guarantee of synchronous invocation
/// enables the function to mutate data under the expectation of exclusive
/// access (we formalize this guarantee as [`FnMut`]). While Rust closures
/// cannot be converted into C function pointers automatically, hyperscan also
/// passes in a `*mut c_void` context pointer to each invocation of the match
/// callback, and this can be used to hold a type-erased container for a
/// Rust-level closure.
///
/// ## Ephemeral Match Objects
/// In all of these synchronous search methods, the provided match callback `f`
/// is converted into a `dyn` reference and invoked within the C function
/// pointer provided to the hyperscan library. Match objects like [`Match`]
/// provided to the match callback are synthesized by this crate and are not
/// preserved after each invocation of `f`, so the match callback must modify
/// some external state to store match results.
impl Scratch {
  /// Synchronously scan a single contiguous string.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, error::*};
  ///
  ///   let a_expr: Expression = "a+".parse()?;
  ///   let b_expr: Expression = "b+".parse()?;
  ///   let flags = Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///     .with_flags([flags, flags])
  ///     .with_ids([ExprId(1), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   {
  ///     let mut f = |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     };
  ///     scratch.scan_sync(&db, "aardvark".into(), &mut f)?;
  ///     scratch.scan_sync(&db, "imbibbe".into(), &mut f)?;
  ///   }
  ///   assert_eq!(&matches, &["a", "aa", "a", "b", "b", "bb"]);
  ///
  ///   let ret = scratch.scan_sync(&db, "abwuebiaubeb".into(), |_| MatchResult::CeaseMatching);
  ///   assert!(matches![ret, Err(HyperscanRuntimeError::ScanTerminated)]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_sync<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    mut f: impl FnMut(Match<'data>) -> MatchResult,
  ) -> Result<(), HyperscanRuntimeError> {
    let mut matcher = SliceMatcher::new(data, &mut f);
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan(
        db.as_ref_native(),
        matcher.parent_slice().as_ptr(),
        matcher.parent_slice().native_len(),
        /* NB: ignoring flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice),
        mem::transmute(&mut matcher),
      )
    })
  }

  /// Synchronously scan a slice of vectored string data.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, sources::*, matchers::{*, vectored_slice::*}};
  ///
  ///   let a_plus: Expression = "a+".parse()?;
  ///   let b_plus: Expression = "b+".parse()?;
  ///   let asdf: Expression = "asdf(.)".parse()?;
  ///   let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_plus, &b_plus, &asdf])
  ///     .with_flags([flags, flags, flags])
  ///     .with_ids([ExprId(0), ExprId(3), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::VECTORED)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let data: [ByteSlice; 4] = [
  ///     "aardvark".into(),
  ///     "imbibbe".into(),
  ///     "leas".into(),
  ///     "dfeg".into(),
  ///   ];
  ///   let mut matches: Vec<(u32, String)> = Vec::new();
  ///   scratch
  ///     .scan_sync_vectored(
  ///       &db,
  ///       data.as_ref().into(),
  ///       |VectoredMatch { id: ExpressionIndex(id), source, .. }| {
  ///         let joined = source.iter_slices()
  ///           .map(|s| unsafe { s.as_str() })
  ///           .collect::<Vec<_>>()
  ///           .concat();
  ///         matches.push((id, joined));
  ///         MatchResult::Continue
  ///     })?;
  ///   assert_eq!(matches, vec![
  ///     (0, "a".to_string()),
  ///     (0, "aa".to_string()),
  ///     (0, "a".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "bb".to_string()),
  ///     (0, "a".to_string()),
  ///     // NB: This match result crosses a slice boundary!
  ///     (2, "asdfe".to_string()),
  ///   ]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_sync_vectored<'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data, 'data>,
    mut f: impl FnMut(VectoredMatch<'data>) -> MatchResult,
  ) -> Result<(), HyperscanRuntimeError> {
    let mut matcher = VectoredMatcher::new(data, &mut f);
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
        Some(match_slice_vectored),
        mem::transmute(&mut matcher),
      )
    })
  }

  /// Write `data` into the stream object `sink`.
  ///
  /// This method is mostly used internally; consumers of this crate will likely
  /// prefer to call [`StreamSink::scan()`].
  pub fn scan_sync_stream<'data>(
    &mut self,
    data: ByteSlice<'data>,
    sink: &mut StreamSink,
  ) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan_stream(
        sink.live.as_mut_native(),
        data.as_ptr(),
        data.native_len(),
        /* NB: ignore flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice_stream),
        mem::transmute(&mut sink.matcher),
      )
    })
  }

  /// Process any EOD (end-of-data) matches for the stream object `sink`.
  ///
  /// This method is mostly used internally; consumers of this crate will likely
  /// prefer to call [`StreamSink::flush_eod()`].
  pub fn flush_eod_sync(&mut self, sink: &mut StreamSink) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_direct_flush_stream(
        sink.live.as_mut_native(),
        self.as_mut_native().unwrap(),
        Some(match_slice_stream),
        mem::transmute(&mut sink.matcher),
      )
    })
  }
}

/// # Asynchronous String Scanning
/// Because the match callback from [Synchronous String
/// Scanning](#synchronous-string-scanning) is invoked synchronously, it also
/// stops the regex engine from making any further progress while it executes,
/// which can harm search performance via cache effects. One common pattern is
/// to write the match object to a queue, then read it from a separate thread to
/// decouple match processing from text searching. `async` streams provide a
/// natural way to achieve this, so these methods use a channel to
/// implement a producer-consumer pattern for this use case. The match callback
/// for these methods accepts a reference to the match object to clarify that
/// the callback only determines whether to continue matching, while the
/// underlying match object is written into the stream and should be retrieved
/// from there instead.
#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
impl Scratch {
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
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  ///   use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, error::*};
  ///   use futures_util::TryStreamExt;
  ///
  ///   let a_expr: Expression = "a+".parse()?;
  ///   let b_expr: Expression = "b+".parse()?;
  ///   let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///     .with_flags([flags, flags])
  ///     .with_ids([ExprId(1), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let matches: Vec<&str> = scratch
  ///     .scan_channel(&db, "aardvark".into(), |_| MatchResult::Continue)
  ///     .and_then(|Match { source, .. }| async move { Ok(unsafe { source.as_str() }) })
  ///     .try_collect()
  ///     .await?;
  ///   assert_eq!(&matches, &["a", "aa", "a"]);
  ///
  ///   let matches: Vec<&str> = scratch
  ///     .scan_channel(&db, "imbibbe".into(), |_| MatchResult::Continue)
  ///     .and_then(|Match { source, .. }| async move { Ok(unsafe { source.as_str() }) })
  ///     .try_collect()
  ///     .await?;
  ///   assert_eq!(&matches, &["b", "b", "bb"]);
  ///
  ///   let ret = scratch.scan_channel(
  ///     &db,
  ///     "abwuebiaubeb".into(),
  ///     |_| MatchResult::CeaseMatching,
  ///   ).try_for_each(|_| async { Ok(()) })
  ///    .await;
  ///   assert!(matches![ret, Err(ScanError::ReturnValue(HyperscanRuntimeError::ScanTerminated))]);
  ///   Ok(())
  /// })}
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_channel<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    mut f: impl FnMut(&Match<'data>) -> MatchResult+Send+Sync,
  ) -> impl Stream<Item=Result<Match<'data>, ScanError>> {
    /* Convert all references into pointers cast to usize to strip lifetime
     * information so it can be moved into spawn_blocking(): */
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);
    let f: &mut (dyn FnMut(&Match<'data>) -> MatchResult+Send+Sync) = &mut f;

    /* Create a channel for both success and error results. */
    let (matches_tx, matches_rx) = mpsc::unbounded_channel();

    /* Convert parameterized lifetimes to 'static so they can be moved into
     * spawn_blocking(): */
    let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
    let f: &'static mut (dyn FnMut(&Match<'static>) -> MatchResult+Send+Sync) =
      unsafe { mem::transmute(f) };
    let matches_tx: mpsc::UnboundedSender<Result<Match<'static>, ScanError>> =
      unsafe { mem::transmute(matches_tx) };

    let matches_tx2 = matches_tx.clone();
    let scan_task = task::spawn_blocking(move || {
      /* Dereference pointer arguments. */
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);

      scratch.scan_sync(db, data, |m| {
        let result = f(&m);
        matches_tx2.send(Ok(m)).unwrap();
        result
      })
    });
    task::spawn(async move {
      match scan_task.await {
        Ok(Ok(())) => (),
        Err(e) => matches_tx.send(Err(e.into())).unwrap(),
        Ok(Err(e)) => matches_tx.send(Err(e.into())).unwrap(),
      }
    });
    async_utils::UnboundedReceiverStream(matches_rx)
  }

  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  ///   use hyperscan::{expression::*, flags::*, sources::*, matchers::{*, vectored_slice::*}};
  ///   use futures_util::TryStreamExt;
  ///
  ///   let a_plus: Expression = "a+".parse()?;
  ///   let b_plus: Expression = "b+".parse()?;
  ///   let asdf: Expression = "asdf(.)".parse()?;
  ///   let flags = Flags::UTF8 | Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_plus, &b_plus, &asdf])
  ///     .with_flags([flags, flags, flags])
  ///     .with_ids([ExprId(0), ExprId(3), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::VECTORED)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let data: [ByteSlice; 4] = [
  ///     "aardvark".into(),
  ///     "imbibbe".into(),
  ///     "leas".into(),
  ///     "dfeg".into(),
  ///   ];
  ///   let matches: Vec<(u32, String)> = scratch
  ///     .scan_channel_vectored(&db, data.as_ref().into(), |_| MatchResult::Continue)
  ///     .and_then(|VectoredMatch { id: ExpressionIndex(id), source, .. }| async move {
  ///       let joined = source.iter_slices()
  ///         .map(|s| unsafe { s.as_str() })
  ///         .collect::<Vec<_>>()
  ///         .concat();
  ///       Ok((id, joined))
  ///     })
  ///     .try_collect()
  ///     .await?;
  ///   assert_eq!(matches, vec![
  ///     (0, "a".to_string()),
  ///     (0, "aa".to_string()),
  ///     (0, "a".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "bb".to_string()),
  ///     (0, "a".to_string()),
  ///     // NB: This match result crosses a slice boundary!
  ///     (2, "asdfe".to_string()),
  ///   ]);
  ///   Ok(())
  /// })}
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_channel_vectored<'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data, 'data>,
    mut f: impl FnMut(&VectoredMatch<'data>) -> MatchResult+Send+Sync,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, ScanError>> {
    /* NB: while static arrays take up no extra runtime space, a ref to a
    slice
    * takes up more than pointer space! */
    static_assertions::assert_eq_size!([u8; 4], u32);
    static_assertions::assert_eq_size!(&u8, *const u8);
    static_assertions::assert_eq_size!(&[u8; 4], *const u8);
    static_assertions::const_assert!(mem::size_of::<&[u8]>() > mem::size_of::<*const u8>());
    static_assertions::assert_eq_size!(&u8, *const u8);

    /* Convert all references into pointers cast to usize to strip lifetime
     * information so it can be moved into spawn_blocking(): */
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);
    let f: &mut (dyn FnMut(&VectoredMatch<'data>) -> MatchResult+Send+Sync) = &mut f;

    /* Create a channel for both success and error results. */
    let (matches_tx, matches_rx) = mpsc::unbounded_channel();

    /* Convert parameterized lifetimes to 'static so they can be moved into
     * spawn_blocking(): */
    let data: VectoredByteSlices<'static, 'static> = unsafe { mem::transmute(data) };
    let f: &'static mut (dyn FnMut(&VectoredMatch<'static>) -> MatchResult+Send+Sync) =
      unsafe { mem::transmute(f) };
    let matches_tx: mpsc::UnboundedSender<Result<VectoredMatch<'static>, ScanError>> =
      unsafe { mem::transmute(matches_tx) };

    let matches_tx2 = matches_tx.clone();
    let scan_task = task::spawn_blocking(move || {
      /* Dereference pointer arguments. */
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);

      scratch.scan_sync_vectored(db, data, |m| {
        let result = f(&m);
        matches_tx2.send(Ok(m)).unwrap();
        result
      })
    });
    task::spawn(async move {
      match scan_task.await {
        Ok(Ok(())) => (),
        Err(e) => matches_tx.send(Err(e.into())).unwrap(),
        Ok(Err(e)) => matches_tx.send(Err(e.into())).unwrap(),
      }
    });
    async_utils::UnboundedReceiverStream(matches_rx)
  }

  pub async fn scan_stream<'data>(
    &mut self,
    data: ByteSlice<'data>,
    sink: &mut StreamSinkChannel,
  ) -> Result<(), ScanError> {
    let s: &'static mut Self = unsafe { mem::transmute(self) };
    let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
    let sink: &'static mut StreamSinkChannel = unsafe { mem::transmute(sink) };

    Ok(
      task::spawn_blocking(move || {
        HyperscanRuntimeError::from_native(unsafe {
          hs::hs_scan_stream(
            sink.live.as_mut_native(),
            data.as_ptr(),
            data.native_len(),
            /* NB: ignore flags for now! */
            0,
            s.as_mut_native().unwrap(),
            Some(scan_slice_stream),
            mem::transmute(&mut sink.matcher),
          )
        })
      })
      .await??,
    )
  }

  pub async fn flush_eod(&mut self, sink: &mut StreamSinkChannel) -> Result<(), ScanError> {
    let s: &'static mut Self = unsafe { mem::transmute(self) };
    let sink: &'static mut StreamSinkChannel = unsafe { mem::transmute(sink) };

    Ok(
      task::spawn_blocking(move || {
        HyperscanRuntimeError::from_native(unsafe {
          hs::hs_direct_flush_stream(
            sink.live.as_mut_native(),
            s.as_mut_native().unwrap(),
            Some(scan_slice_stream),
            mem::transmute(&mut sink.matcher),
          )
        })
      })
      .await??,
    )
  }
}

/// # Managing Allocations
/// These methods provide access to the underlying memory allocation
/// containing the data for the scratch space. They can be used to
/// control the memory location used for the scratch space, or to preserve
/// scratch allocations across weird lifetime constraints.
///
/// Note that [`Self::scratch_size()`] can be used to determine the size of
/// the memory allocation pointed to by [`Self::as_ref_native()`] and
/// [`Self::as_mut_native()`].
impl Scratch {
  /* TODO: NonNull::new is not const yet! */
  /// Wrap the provided allocation `p`.
  ///
  /// # Safety
  /// The pointer `p` must be null or have been produced by
  /// [`Self::as_mut_native()`].
  ///
  /// This method also makes it especially easy to create multiple references to
  /// the same allocation, which will then cause a double free when
  /// [`Self::try_drop()`] is called more than once for the same scratch
  /// allocation. To avoid this, wrap the result in a
  /// [`ManuallyDrop`](mem::ManuallyDrop):
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, state::*};
  ///   use std::{mem::ManuallyDrop, ptr};
  ///
  ///   // Compile a legitimate db:
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   // Create two new references to that allocation,
  ///   // wrapped to avoid calling the drop code:
  ///   let scratch_ptr: *mut NativeScratch = scratch
  ///     .as_mut_native()
  ///     .map(|p| p as *mut NativeScratch)
  ///     .unwrap_or(ptr::null_mut());
  ///   let mut scratch_ref_1 = ManuallyDrop::new(unsafe { Scratch::from_native(scratch_ptr) });
  ///   let mut scratch_ref_2 = ManuallyDrop::new(unsafe { Scratch::from_native(scratch_ptr) });
  ///
  ///   // Both scratch references are valid and can be used for matching.
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch_ref_1
  ///     .scan_sync(&db, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   scratch_ref_2
  ///     .scan_sync(&db, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "aa", "a", "a", "aa", "a"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub unsafe fn from_native(p: *mut NativeScratch) -> Self { Self(NonNull::new(p)) }

  /// Get a read-only reference to the scratch allocation.
  ///
  /// This method is mostly used internally and converted to a nullable pointer
  /// to provide to the hyperscan native library methods.
  pub fn as_ref_native(&self) -> Option<&NativeScratch> { self.0.map(|p| unsafe { p.as_ref() }) }

  /// Get a mutable reference to the scratch allocation.
  ///
  /// The result of this method can be converted to a nullable pointer and
  /// provided to [`Self::from_native()`].
  pub fn as_mut_native(&mut self) -> Option<&mut NativeScratch> {
    self.0.map(|mut p| unsafe { p.as_mut() })
  }

  /// Return the size of the scratch allocation.
  ///
  /// Using [`Flags::UCP`](crate::flags::Flags::UCP) explodes the size of
  /// character classes, which increases the size of the scratch space:
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let ascii_db = expr.compile(Flags::default(), Mode::BLOCK)?;
  ///
  ///   let utf8_scratch = utf8_db.allocate_scratch()?;
  ///   let ascii_scratch = ascii_db.allocate_scratch()?;
  ///
  ///   // Including UTF-8 classes increases the size:
  ///   assert!(utf8_scratch.scratch_size()? > ascii_scratch.scratch_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  ///
  /// This size corresponds to the requested allocation size passed to the db
  /// allocator:
  ///
  ///```
  /// #[cfg(all(feature = "alloc", feature = "compiler"))]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, state::*, alloc::*};
  ///   use std::alloc::System;
  ///
  ///   // Wrap the standard Rust System allocator.
  ///   let tracker = LayoutTracker::new(System.into());
  ///   // Register it as the allocator for databases.
  ///   assert!(set_scratch_allocator(tracker)?.is_none());
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let mut utf8_scratch = utf8_db.allocate_scratch()?;
  ///
  ///   // Get the scratch allocator we just registered and view its live allocations:
  ///   let allocs = get_scratch_allocator().as_ref().unwrap().current_allocations();
  ///   // Verify that only the single known scratch was allocated:
  ///   assert_eq!(1, allocs.len());
  ///   let (p, layout) = allocs[0];
  ///   // The allocation was made 30 bytes to the left of the returned scratch pointer.
  ///   assert_eq!(
  ///     unsafe { p.as_ptr().add(0x30) },
  ///     utf8_scratch.as_mut_native().unwrap() as *mut NativeScratch as *mut u8,
  ///   );
  ///
  ///   // Verify that the allocation size is the same as reported:
  ///   assert_eq!(layout.size(), utf8_scratch.scratch_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(all(feature = "alloc", feature = "compiler")))]
  /// # fn main() {}
  /// ```
  pub fn scratch_size(&self) -> Result<usize, HyperscanRuntimeError> {
    match self.as_ref_native() {
      None => Ok(0),
      Some(p) => {
        let mut n: usize = 0;
        HyperscanRuntimeError::from_native(unsafe { hs::hs_scratch_size(p, &mut n) })?;
        Ok(n)
      },
    }
  }

  /// Generate a new scratch space which can be applied to the same databases as
  /// the original.
  ///
  /// This new scratch space is allocated in a new region of memory provided by
  /// the scratch allocator. This is used to implement [`Clone`].
  ///
  ///```
  /// #[cfg(all(feature = "alloc", feature = "compiler"))]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, alloc::*};
  ///   use std::alloc::System;
  ///
  ///   // Wrap the standard Rust System allocator.
  ///   let tracker = LayoutTracker::new(System.into());
  ///   // Register it as the allocator for databases.
  ///   assert!(set_scratch_allocator(tracker)?.is_none());
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let scratch1 = utf8_db.allocate_scratch()?;
  ///   let _scratch2 = scratch1.try_clone()?;
  ///
  ///   // Get the database allocator we just registered and view its live allocations:
  ///   let allocs = get_scratch_allocator().as_ref().unwrap().current_allocations();
  ///   // Verify that only two scratches were allocated:
  ///   assert_eq!(2, allocs.len());
  ///   let (p1, l1) = allocs[0];
  ///   let (p2, l2) = allocs[1];
  ///   assert!(p1 != p2);
  ///   assert!(l1 == l2);
  ///   Ok(())
  /// }
  /// # #[cfg(not(all(feature = "alloc", feature = "compiler")))]
  /// # fn main() {}
  /// ```
  pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
    match self.as_ref_native() {
      None => Ok(Self::blank()),
      Some(p) => {
        let mut scratch_ptr = ptr::null_mut();
        HyperscanRuntimeError::from_native(unsafe { hs::hs_clone_scratch(p, &mut scratch_ptr) })?;
        Ok(Self(NonNull::new(scratch_ptr)))
      },
    }
  }

  /// Free the underlying scratch allocation.
  ///
  /// # Safety
  /// This method must be called at most once over the lifetime of each scratch
  /// allocation. It is called by default on drop, so
  /// [`ManuallyDrop`](mem::ManuallyDrop) is recommended to wrap
  /// instances that reference external data in order to avoid attempting to
  /// free the referenced data.
  ///
  /// Because the pointer returned by [`Self::as_mut_native()`] does not
  /// correspond to the entire scratch allocation, this method *must* be
  /// executed in order to avoid leaking resources associated with a scratch
  /// space. The memory *must not* be deallocated elsewhere.
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

#[cfg(all(test, feature = "compiler", feature = "async"))]
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
      .scan_channel(&db, "asdf".into(), |_| MatchResult::Continue)
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
      .scan_channel(&db, "asdf".into(), |_| MatchResult::Continue)
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

  pub type NativeChimeraScratch = hs::ch_scratch;

  #[derive(Debug)]
  #[repr(transparent)]
  pub struct ChimeraScratch(Option<NonNull<NativeChimeraScratch>>);

  impl ChimeraScratch {
    pub const fn blank() -> Self { Self(None) }

    pub fn setup_for_db(&mut self, db: &ChimeraDb) -> Result<(), ChimeraRuntimeError> {
      let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
      })?;
      self.0 = NonNull::new(scratch_ptr);
      Ok(())
    }
  }

  impl ChimeraScratch {
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
          Some(match_chimera_slice),
          Some(error_callback_chimera),
          mem::transmute(&mut matcher),
        )
      })
    }
  }

  impl ChimeraScratch {
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
    /// let matches: Vec<(&str, &str)> = scratch.scan_channel(&db, "aardvark".into(), m, e)
    ///  .and_then(|ChimeraMatch { source, captures, .. }| async move {
    ///    Ok(unsafe { (source.as_str(), captures[1].unwrap().as_str()) })
    ///  })
    ///  .try_collect()
    ///  .await?;
    /// assert_eq!(&matches, &[("aar", "r"), ("ar", "r")]);
    /// # Ok(())
    /// # })}
    /// ```
    #[cfg(feature = "async")]
    #[cfg_attr(docsrs, doc(cfg(feature = "async")))]
    pub fn scan_channel<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
      mut m: impl FnMut(&ChimeraMatch<'data>) -> ChimeraMatchResult+Send+Sync,
      mut e: impl FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync,
    ) -> impl Stream<Item=Result<ChimeraMatch<'data>, ChimeraScanError>> {
      /* Convert all references into pointers cast to usize to strip lifetime
       * information so it can be moved into spawn_blocking(): */
      let scratch = Self::into_scratch(self);
      let db = Self::into_db(db);
      let m: &mut (dyn FnMut(&ChimeraMatch<'data>) -> ChimeraMatchResult+Send+Sync) = &mut m;
      let e: &mut (dyn FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync) = &mut e;

      /* Create a channel for all success and error results. */
      let (matches_tx, matches_rx) = mpsc::unbounded_channel();

      /* Convert parameterized lifetimes to 'static so they can be moved into
       * spawn_blocking(): */
      let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
      let m: &'static mut (dyn FnMut(&ChimeraMatch<'static>) -> ChimeraMatchResult+Send+Sync) =
        unsafe { mem::transmute(m) };
      let e: &'static mut (dyn FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync) =
        unsafe { mem::transmute(e) };
      let matches_tx: mpsc::UnboundedSender<Result<ChimeraMatch<'static>, ChimeraScanError>> =
        unsafe { mem::transmute(matches_tx) };

      let matches_tx2 = matches_tx.clone();
      let scan_task = task::spawn_blocking(move || {
        /* Dereference pointer arguments. */
        let scratch: &mut Self = Self::from_scratch(scratch);
        let db: &ChimeraDb = Self::from_db(db);

        scratch.scan_sync(
          db,
          data,
          |cm| {
            let result = m(&cm);
            matches_tx2.send(Ok(cm)).unwrap();
            result
          },
          |ce| {
            let result = e(&ce);
            matches_tx2.send(Err(ce.into())).unwrap();
            result
          },
        )
      });
      task::spawn(async move {
        match scan_task.await {
          Ok(Ok(())) => (),
          Err(e) => matches_tx.send(Err(e.into())).unwrap(),
          Ok(Err(e)) => matches_tx.send(Err(e.into())).unwrap(),
        }
      });
      async_utils::UnboundedReceiverStream(matches_rx)
    }
  }

  impl ChimeraScratch {
    pub fn as_ref_native(&self) -> Option<&NativeChimeraScratch> {
      self.0.map(|p| unsafe { p.as_ref() })
    }

    pub fn as_mut_native(&mut self) -> Option<&mut NativeChimeraScratch> {
      self.0.map(|mut p| unsafe { p.as_mut() })
    }

    pub fn scratch_size(&self) -> Result<usize, ChimeraRuntimeError> {
      match self.as_ref_native() {
        None => Ok(0),
        Some(p) => {
          let mut n: usize = 0;
          ChimeraRuntimeError::from_native(unsafe { hs::ch_scratch_size(p, &mut n) })?;
          Ok(n)
        },
      }
    }

    pub fn try_clone(&self) -> Result<Self, ChimeraRuntimeError> {
      match self.as_ref_native() {
        None => Ok(Self::blank()),
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

#[cfg(feature = "async")]
mod async_utils {
  use futures_core::stream::Stream;
  use tokio::sync::mpsc;

  use std::{
    pin::Pin,
    task::{Context, Poll},
  };

  /* Reimplementation of tokio_stream::wrappers::UnboundedReceiverStream. */
  #[derive(Debug)]
  #[repr(transparent)]
  pub struct UnboundedReceiverStream<T>(pub mpsc::UnboundedReceiver<T>);

  impl<T> Stream for UnboundedReceiverStream<T> {
    type Item = T;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
      self.0.poll_recv(cx)
    }
  }
}

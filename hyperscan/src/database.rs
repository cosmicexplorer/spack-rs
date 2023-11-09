/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  error::{HyperscanCompileError, HyperscanError, HyperscanFlagsError},
  expression::{Expression, ExpressionSet},
  flags::{Flags, Mode, ScanFlags},
  hs,
  matchers::{
    contiguous_slice::{match_slice_ref, Match, Scanner, SliceMatcher},
    vectored_slice::{
      match_slice_vectored_ref, VectorScanner, VectoredMatch, VectoredSliceMatcher,
    },
    ByteSlice, VectoredByteSlices,
  },
  state::{Platform, Scratch},
};

use async_stream::try_stream;
use futures_core::stream::Stream;
use futures_util::{pin_mut, StreamExt};
use tokio::task;
use tokio_stream::wrappers::ReceiverStream;

use std::{
  mem, ops,
  os::raw::{c_char, c_uint, c_void},
  pin::Pin,
  ptr,
};

#[derive(Debug)]
pub struct Database(*mut hs::hs_database);

impl AsRef<hs::hs_database> for Database {
  fn as_ref(&self) -> &hs::hs_database { unsafe { &*self.0 } }
}

impl AsMut<hs::hs_database> for Database {
  fn as_mut(&mut self) -> &mut hs::hs_database { unsafe { &mut *self.0 } }
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

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*, state::*};
  /// use futures_util::TryStreamExt;
  /// use std::pin::Pin;
  ///
  /// let expr = Expression::new("(he)ll")?;
  /// let flags = Flags::UTF8;
  /// let mode = Mode::BLOCK;
  /// let db = Database::compile(&expr, flags, mode)?;
  ///
  /// let mut scratch = Scratch::alloc(Pin::new(&db))?;
  ///
  /// let data = ByteSlice(b"hello");
  /// let scan_flags = ScanFlags::default();
  /// let matches: Vec<&str> = scratch
  ///   .scan(data, scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.decode_utf8().unwrap()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["hell"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn compile(
    expression: &Expression,
    flags: Flags,
    mode: Mode,
  ) -> Result<Self, HyperscanCompileError> {
    let (flags, mode) = Self::validate_flags_and_mode(flags, mode)?;
    let platform = Platform::get();

    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile(
          expression.as_ptr(),
          flags,
          mode,
          platform.as_ref(),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(Self(db))
  }

  pub fn compile_multi(
    expression_set: &ExpressionSet,
    mode: Mode,
  ) -> Result<Self, HyperscanCompileError> {
    mode.validate_db_type()?;
    let platform = Platform::get();

    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        if let Some(exts_ptr) = expression_set.exts_ptr() {
          hs::hs_compile_ext_multi(
            expression_set.expressions_ptr(),
            expression_set.flags_ptr(),
            expression_set.ids_ptr(),
            exts_ptr,
            expression_set.num_elements(),
            mode.into_native(),
            platform.as_ref(),
            &mut db,
            &mut compile_err,
          )
        } else {
          hs::hs_compile_multi(
            expression_set.expressions_ptr(),
            expression_set.flags_ptr(),
            expression_set.ids_ptr(),
            expression_set.num_elements(),
            mode.into_native(),
            platform.as_ref(),
            &mut db,
            &mut compile_err,
          )
        }
      },
      compile_err,
    )?;
    Ok(Self(db))
  }

  pub(crate) fn scan_matches<'data, F: Scanner<'data>>(
    self: Pin<&Self>,
    data: ByteSlice<'data>,
    flags: ScanFlags,
    scratch: &mut Scratch,
    mut f: F,
  ) -> impl Stream<Item=Result<Match<'data>, HyperscanError>>+'data {
    let data_len = data.len();
    let data_pointer: *const c_char = data.as_ptr();

    let (matcher, mut matches_rx) = SliceMatcher::new::<32, _>(data, &mut f);
    let ctx: *mut SliceMatcher = Box::into_raw(Box::new(matcher));
    let ctx: usize = ctx as usize;

    let s: &Self = &self.as_ref();
    let s: *const hs::hs_database = s.as_ref();
    let s: usize = unsafe { mem::transmute(s) };
    let data: usize = data_pointer as usize;
    let scratch: *mut hs::hs_scratch = scratch.as_mut();
    let scratch: usize = scratch as usize;

    let scan_task = task::spawn_blocking(move || {
      let mut matcher: Pin<Box<SliceMatcher>> =
        Box::into_pin(unsafe { Box::from_raw(ctx as *mut SliceMatcher) });
      HyperscanError::from_native(unsafe {
        hs::hs_scan(
          s as *const hs::hs_database,
          data as *const c_char,
          data_len,
          flags.into_native(),
          scratch as *mut hs::hs_scratch,
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

  /* pub fn scan_vector<'data, F: VectorScanner<'data>>( */
  /* &self, */
  /* data: VectoredByteSlices<'data>, */
  /* flags: ScanFlags, */
  /* scratch: &mut Scratch, */
  /* mut f: F, */
  /* ) -> impl Stream<Item=Result<VectoredMatch<'data>, HyperscanError>>+'data
   * { */
  /* /\* NB: while static arrays take up no extra runtime space, a ref to a
   * slice */
  /* * takes up more than pointer space! *\/ */
  /* static_assertions::assert_eq_size!([u8; 4], u32); */
  /* static_assertions::assert_eq_size!(&u8, *const u8); */
  /* static_assertions::const_assert_ne!(mem::size_of::<&[u8]>(),
   * mem::size_of::<*const u8>()); */

  /* let data_len = data.len(); */
  /* let (data_pointers, lengths) = data.pointers_and_lengths(); */

  /* let f: &'static mut u8 = unsafe { mem::transmute(&mut f) }; */
  /* let mut matcher = VectoredSliceMatcher::new::<F>(data, unsafe {
   * mem::transmute(f) }); */

  /* let s: &hs::hs_database = self.as_ref(); */
  /* let s: usize = unsafe { mem::transmute(s) }; */
  /* let data: *const *const c_char = data_pointers.as_ptr(); */
  /* let data: usize = unsafe { mem::transmute(data) }; */
  /* let scratch: &mut hs::hs_scratch = scratch.as_mut(); */
  /* let scratch: usize = unsafe { mem::transmute(scratch) }; */

  /* let ctx: usize = unsafe { mem::transmute(&mut matcher) }; */
  /* let scan_task = task::spawn_blocking(move || { */
  /* HyperscanError::from_native(unsafe { */
  /* hs::hs_scan_vector( */
  /* s as *const hs::hs_database, */
  /* data as *const *const c_char, */
  /* lengths.as_ptr(), */
  /* data_len, */
  /* flags.into_native(), */
  /* scratch as *mut hs::hs_scratch, */
  /* Some(match_slice_vectored_ref), */
  /* ctx as *mut c_void, */
  /* ) */
  /* }) */
  /* }); */

  /* try_stream! { */
  /* let mut matcher = Pin::new(&mut matcher); */
  /* while !scan_task.is_finished() { */
  /* yield matcher.as_mut().await; */
  /* } */
  /* for m in matcher.pop_rest().into_iter() { */
  /* yield m; */
  /* } */
  /* scan_task.await.unwrap()?; */
  /* } */
  /* } */

  pub fn try_drop(&mut self) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_database(self.as_mut()) })
  }
}

impl ops::Drop for Database {
  fn drop(&mut self) { self.try_drop().unwrap(); }
}

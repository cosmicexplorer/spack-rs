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
pub use flags::{CpuFeatures, Flags, Mode, ScanFlags, TuneFamily};

mod state;
pub use state::{Platform, Scratch};

mod expression;
pub use expression::{ExprInfo, ExprWidth, Expression, MatchAtEndBehavior, UnorderedMatchBehavior};

pub(crate) use bindings as hs;

use async_stream::try_stream;
use futures_core::stream::Stream;
use tokio::task;

use std::{
  ffi::CString,
  mem, ops,
  os::raw::{c_char, c_uint, c_void},
  pin::Pin,
};

mod matchers;
use matchers::{
  contiguous_slice::{match_slice_ref, SliceMatcher},
  vectored_slice::{match_slice_vectored_ref, VectoredSliceMatcher},
};
pub use matchers::{
  contiguous_slice::{Match, Scanner},
  vectored_slice::{VectorScanner, VectoredMatch},
  ByteSlice, VectoredByteSlices,
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
    expression: Vec<u8>,
    flags: Flags,
    mode: Mode,
  ) -> Result<Self, HyperscanCompileError> {
    let (flags, mode) = Self::validate_flags_and_mode(flags, mode)?;
    let platform = Platform::get();

    let expression = CString::new(expression)?;

    let mut db = mem::MaybeUninit::<hs::hs_database>::uninit();
    let mut compile_err = mem::MaybeUninit::<hs::hs_compile_error>::uninit();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile(
          expression.as_c_str().as_ptr(),
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
    let data_len = data.len();
    let data_pointer: *const c_char = data.as_ptr();

    let f: &'static mut u8 = unsafe { mem::transmute(&mut f) };
    let mut matcher = SliceMatcher::new::<F>(data, unsafe { mem::transmute(f) });

    let s: &hs::hs_database = self.as_ref();
    let s: usize = unsafe { mem::transmute(s) };
    let data: usize = unsafe { mem::transmute(data_pointer) };
    let scratch: &mut hs::hs_scratch = scratch.as_mut();
    let scratch: usize = unsafe { mem::transmute(scratch) };

    let ctx: usize = unsafe { mem::transmute(&mut matcher) };
    let scan_task = task::spawn_blocking(move || {
      HyperscanError::from_native(unsafe {
        hs::hs_scan(
          s as *const hs::hs_database,
          data as *const c_char,
          data_len,
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

    let data_len = data.len();
    let (data_pointers, lengths) = data.pointers_and_lengths();

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
          data_len,
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

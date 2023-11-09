/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  error::{HyperscanCompileError, HyperscanError, HyperscanFlagsError},
  expression::{Expression, ExpressionSet},
  flags::{Flags, Mode},
  hs,
  state::Platform,
};

use std::{ops, os::raw::c_uint, pin::Pin, ptr};

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
  /// let scratch = Pin::new(&mut scratch);
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

  fn try_drop(self: Pin<&mut Self>) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_database(self.get_mut().as_mut()) })
  }
}

impl ops::Drop for Database {
  fn drop(&mut self) { Pin::new(self).try_drop().unwrap(); }
}

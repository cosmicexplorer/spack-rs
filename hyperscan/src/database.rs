/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  error::{HyperscanCompileError, HyperscanError, HyperscanFlagsError},
  expression::{Expression, ExpressionSet, Literal, LiteralSet},
  flags::{Flags, Mode},
  hs,
  state::Platform,
};

use libc;

use std::{
  ffi::CStr,
  mem::MaybeUninit,
  ops,
  os::raw::{c_char, c_uint, c_void},
  pin::Pin,
  ptr,
};

#[derive(Debug)]
pub struct Database(*mut hs::hs_database);

impl Database {
  #[inline]
  pub(crate) const fn as_ref_native(&self) -> &hs::hs_database { unsafe { &*self.0 } }

  #[inline]
  pub(crate) const fn as_mut_native(&mut self) -> &mut hs::hs_database { unsafe { &mut *self.0 } }

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
  /// let expr: Expression = "(he)ll".parse()?;
  /// let db = Database::compile(&expr, Flags::UTF8, Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::try_open(Pin::new(&db)).await?;
  /// let scratch = Pin::new(&mut scratch);
  ///
  /// let scan_flags = ScanFlags::default();
  /// let matches: Vec<&str> = scratch
  ///   .scan("hello".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
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
  /// let expr: Literal = "he\0ll".parse()?;
  /// let db = Database::compile_literal(&expr, Flags::default(), Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::try_open(Pin::new(&db)).await?;
  /// let scratch = Pin::new(&mut scratch);
  ///
  /// let scan_flags = ScanFlags::default();
  /// let matches: Vec<&str> = scratch
  ///   .scan("he\0llo".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["he\0ll"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn compile_literal(
    literal: &Literal,
    flags: Flags,
    mode: Mode,
  ) -> Result<Self, HyperscanCompileError> {
    let (flags, mode) = Self::validate_flags_and_mode(flags, mode)?;
    let platform = Platform::get();

    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile_lit(
          literal.as_ptr(),
          flags,
          literal.as_bytes().len(),
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
  /// let a_expr: Expression = "a+".parse()?;
  /// let b_expr: Expression = "b+".parse()?;
  ///
  /// // Example of providing ExprExt info (not available in ::compile()!):
  /// let ext = ExprExt::from_min_length(1);
  ///
  /// let expr_set = ExpressionSet::from_exprs(&[&a_expr, &b_expr])
  ///   .with_flags(&[Flags::UTF8, Flags::UTF8])
  ///   .with_ids(&[ExprId(1), ExprId(2)])
  ///   .with_exts(&[None, Some(&ext)]);
  ///
  /// let db = Database::compile_multi(&expr_set, Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::try_open(Pin::new(&db)).await?;
  /// let mut scratch = Pin::new(&mut scratch);
  ///
  /// let scan_flags = ScanFlags::default();
  ///
  /// let matches: Vec<&str> = scratch
  ///   .as_mut()
  ///   .scan("aardvark".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "aardva"]);
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan("imbibe".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
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

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::{*, contiguous_slice::*}, state::*};
  /// use futures_util::TryStreamExt;
  /// use std::pin::Pin;
  ///
  /// let hell_lit: Literal = "he\0ll".parse()?;
  /// let free_lit: Literal = "fr\0e\0e".parse()?;
  /// let lit_set = LiteralSet::from_lits(&[&hell_lit, &free_lit])
  ///   .with_flags(&[Flags::default(), Flags::default()])
  ///   .with_ids(&[ExprId(2), ExprId(1)]);
  ///
  /// let db = Database::compile_multi_literal(&lit_set, Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::try_open(Pin::new(&db)).await?;
  /// let mut scratch = Pin::new(&mut scratch);
  ///
  /// let scan_flags = ScanFlags::default();
  /// let matches: Vec<(u32, &str)> = scratch
  ///   .as_mut()
  ///   .scan("he\0llo".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|Match { id: ExpressionIndex(id), source, .. }| async move {
  ///     Ok((id, source.as_str()))
  ///   })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &[(2, "he\0ll")]);
  ///
  /// let matches: Vec<(u32, &str)> = scratch
  ///   .scan("fr\0e\0edom".into(), scan_flags, |_| MatchResult::Continue)
  ///   .and_then(|Match { id: ExpressionIndex(id), source, .. }| async move {
  ///     Ok((id, source.as_str()))
  ///   })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &[(1, "fr\0e\0e")]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn compile_multi_literal(
    literal_set: &LiteralSet,
    mode: Mode,
  ) -> Result<Self, HyperscanCompileError> {
    mode.validate_db_type()?;
    let platform = Platform::get();

    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile_lit_multi(
          literal_set.literals_ptr(),
          literal_set.flags_ptr(),
          literal_set.ids_ptr(),
          literal_set.lengths_ptr(),
          literal_set.num_elements(),
          mode.into_native(),
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
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> {
  /// use hyperscan::{expression::*, flags::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
  /// let db_size = db.database_size()?;
  ///
  /// // Size may vary across architectures:
  /// assert_eq!(db_size, 936);
  /// assert!(db_size > 500);
  /// assert!(db_size < 2000);
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn database_size(&self) -> Result<usize, HyperscanError> {
    let mut ret: MaybeUninit<usize> = MaybeUninit::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_database_size(self.as_ref_native(), ret.as_mut_ptr())
    })?;
    Ok(unsafe { ret.assume_init() })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> {
  /// use hyperscan::{expression::*, flags::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::UTF8, Mode::STREAM)?;
  /// let stream_size = db.stream_size()?;
  ///
  /// // Size may vary across architectures:
  /// assert_eq!(stream_size, 18);
  /// assert!(stream_size > 10);
  /// assert!(stream_size < 20);
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn stream_size(&self) -> Result<usize, HyperscanError> {
    let mut ret: MaybeUninit<usize> = MaybeUninit::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_stream_size(self.as_ref_native(), ret.as_mut_ptr())
    })?;
    Ok(unsafe { ret.assume_init() })
  }

  pub fn info(&self) -> Result<DbInfo, HyperscanError> { DbInfo::extract_db_info(self) }

  #[inline]
  fn try_drop(self: Pin<&mut Self>) -> Result<(), HyperscanError> {
    HyperscanError::from_native(unsafe { hs::hs_free_database(self.get_mut().as_mut_native()) })
  }
}

impl ops::Drop for Database {
  fn drop(&mut self) { Pin::new(self).try_drop().unwrap(); }
}

unsafe impl Send for Database {}
unsafe impl Sync for Database {}

#[derive(Debug, Clone)]
pub struct DbInfo(pub String);

impl DbInfo {
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> {
  /// use hyperscan::{expression::*, flags::*, database::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
  /// let info = DbInfo::extract_db_info(&db)?;
  /// assert_eq!(&info.0, "Version: 5.4.2 Features: AVX2 Mode: BLOCK");
  /// # Ok(())
  /// # }
  /// ```
  pub fn extract_db_info(db: &Database) -> Result<Self, HyperscanError> {
    let mut info: MaybeUninit<*mut c_char> = MaybeUninit::uninit();
    HyperscanError::from_native(unsafe {
      hs::hs_database_info(db.as_ref_native(), info.as_mut_ptr())
    })?;
    let info = unsafe { info.assume_init() };
    let ret = unsafe { CStr::from_ptr(info) }
      .to_string_lossy()
      .to_string();
    /* FIXME: make this work with whatever allocator was used! */
    unsafe {
      libc::free(info as *mut c_void);
    }
    Ok(Self(ret))
  }
}

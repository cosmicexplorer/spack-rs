/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  error::{HyperscanCompileError, HyperscanError},
  flags::Flags,
  hs,
};

use std::{
  ffi::CString,
  mem,
  os::raw::{c_char, c_uint},
};

use displaydoc::Display;

pub struct Expression(CString);

impl Expression {
  #[inline]
  pub(crate) fn as_ptr(&self) -> *const c_char { self.0.as_c_str().as_ptr() }

  #[inline]
  pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, HyperscanCompileError> {
    Ok(Self(CString::new(x)?))
  }

  pub fn info(&self, flags: Flags) -> Result<ExprInfo, HyperscanCompileError> {
    let mut info = mem::MaybeUninit::<hs::hs_expr_info>::uninit();
    let mut compile_err = mem::MaybeUninit::<hs::hs_compile_error>::uninit();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_expression_info(
          self.as_ptr(),
          flags.into_native(),
          mem::transmute(&mut info.as_mut_ptr()),
          mem::transmute(&mut compile_err.as_mut_ptr()),
        )
      },
      compile_err.as_mut_ptr(),
    )?;
    let info = ExprInfo::from_native(unsafe { info.assume_init() });
    Ok(info)
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExprWidth(usize);

impl ExprWidth {
  #[inline]
  pub const fn parse_min_width(x: c_uint) -> Self { Self(x as usize) }

  #[inline]
  pub const fn parse_max_width(x: c_uint) -> Option<Self> {
    if x == c_uint::MAX {
      None
    } else {
      Some(Self(x as usize))
    }
  }
}

#[derive(
  Debug,
  Display,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::IntoPrimitive,
  num_enum::FromPrimitive,
)]
#[repr(i8)]
pub enum UnorderedMatchBehavior {
  /// Disallow matches that are not returned in order.
  #[num_enum(default)]
  OnlyOrdered = 0,
  /// Allow matches that are not returned in order.
  AllowUnordered = 1,
}

impl UnorderedMatchBehavior {
  #[inline]
  pub const fn from_native(x: c_char) -> Self {
    if x == 0 {
      Self::OnlyOrdered
    } else {
      Self::AllowUnordered
    }
  }
}

#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(i8)]
pub enum MatchAtEndBehavior {
  /// Disallow matching at EOD.
  NoMatchAtEOD,
  /// Allow matches at EOD.
  AllowMatchAtEOD,
  /// *Only* allow matches at EOD.
  OnlyMatchAtEOD,
}

impl MatchAtEndBehavior {
  #[inline]
  pub const fn from_native(matches_at_eod: c_char, matches_only_at_eod: c_char) -> Self {
    match (matches_at_eod, matches_only_at_eod) {
      (0, 0) => Self::NoMatchAtEOD,
      (1, 0) => Self::AllowMatchAtEOD,
      (0, 1) => Self::OnlyMatchAtEOD,
      _ => unreachable!(),
    }
  }
}

pub struct ExprInfo {
  pub min_width: ExprWidth,
  pub max_width: Option<ExprWidth>,
  /// Whether this expression can produce matches that are not returned in
  /// order, such as those produced by assertions.
  pub unordered_matches: UnorderedMatchBehavior,
  /// Whether this expression can produce matches at end of data (EOD). In
  /// streaming mode, EOD matches are raised during @ref hs_close_stream(),
  /// since it is only when @ref hs_close_stream() is called that the EOD
  /// location is known.
  ///
  /// Note: trailing `\b` word boundary assertions may also result in EOD
  /// matches as end-of-data can act as a word boundary.
  pub matches_at_eod: MatchAtEndBehavior,
}

impl ExprInfo {
  #[inline]
  pub(crate) const fn from_native(x: hs::hs_expr_info) -> Self {
    let hs::hs_expr_info {
      min_width,
      max_width,
      unordered_matches,
      matches_at_eod,
      matches_only_at_eod,
    } = x;
    let min_width = ExprWidth::parse_min_width(min_width);
    let max_width = ExprWidth::parse_max_width(max_width);
    let unordered_matches = UnorderedMatchBehavior::from_native(unordered_matches);
    let matches_at_eod = MatchAtEndBehavior::from_native(matches_at_eod, matches_only_at_eod);
    Self {
      min_width,
      max_width,
      unordered_matches,
      matches_at_eod,
    }
  }
}

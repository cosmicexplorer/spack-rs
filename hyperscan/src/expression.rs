/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::{HyperscanCompileError, HyperscanError},
  flags::{ExtFlags, Flags, Mode},
  hs,
};

use displaydoc::Display;

use std::{
  ffi::CString,
  fmt,
  marker::PhantomData,
  mem, ops,
  os::raw::{c_char, c_uint, c_ulonglong},
  ptr, str,
};

#[derive(Clone)]
pub struct Expression(CString);

impl fmt::Debug for Expression {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.try_decode_utf8() {
      Ok(s) => write!(f, "Expression({:?})", s),
      Err(_) => write!(f, "Expression({:?})", self.as_bytes()),
    }
  }
}

impl Expression {
  #[inline]
  pub fn as_bytes(&self) -> &[u8] { self.0.as_bytes() }

  #[inline]
  fn try_decode_utf8(&self) -> Result<&str, str::Utf8Error> { str::from_utf8(self.as_bytes()) }

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

  pub fn ext_info(
    &self,
    flags: Flags,
    ext_flags: &ExprExt,
  ) -> Result<ExprInfo, HyperscanCompileError> {
    let mut info = mem::MaybeUninit::<hs::hs_expr_info>::uninit();
    let mut compile_err = mem::MaybeUninit::<hs::hs_compile_error>::uninit();
    HyperscanError::copy_from_native_compile_error(
      unsafe {
        hs::hs_expression_ext_info(
          self.as_ptr(),
          flags.into_native(),
          ext_flags.as_ref(),
          mem::transmute(&mut info.as_mut_ptr()),
          mem::transmute(&mut compile_err.as_mut_ptr()),
        )
      },
      compile_err.as_mut_ptr(),
    )?;
    let info = ExprInfo::from_native(unsafe { info.assume_init() });
    Ok(info)
  }

  pub fn compile(&self, flags: Flags, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile(self, flags, mode)
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExprId(c_uint);

#[derive(Debug, Clone)]
pub struct ExpressionSet<'a> {
  ptrs: Vec<*const c_char>,
  flags: Option<Vec<Flags>>,
  ids: Option<Vec<ExprId>>,
  exts: Option<Vec<*const hs::hs_expr_ext>>,
  _ph: PhantomData<&'a u8>,
}

impl<'a> ExpressionSet<'a> {
  pub fn from_exprs(exprs: &[&'a Expression]) -> Self {
    Self {
      ptrs: exprs.iter().map(|e| e.as_ptr()).collect(),
      flags: None,
      ids: None,
      exts: None,
      _ph: PhantomData,
    }
  }

  pub fn with_flags(&mut self, flags: &[Flags]) {
    assert_eq!(self.ptrs.len(), flags.len());
    self.flags = Some(flags.iter().cloned().collect());
  }

  pub fn with_ids(&mut self, ids: &[ExprId]) {
    assert_eq!(self.ptrs.len(), ids.len());
    self.ids = Some(ids.iter().cloned().collect());
  }

  pub fn with_exts(&mut self, exts: &[Option<&'a ExprExt>]) {
    assert_eq!(self.ptrs.len(), exts.len());
    self.exts = Some(
      exts
        .iter()
        .map(|e| {
          e.map(|e| unsafe { mem::transmute(e.as_ref()) })
            .unwrap_or(ptr::null())
        })
        .collect(),
    );
  }

  pub fn compile(self, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_multi(&self, mode)
  }

  #[inline]
  pub(crate) fn num_elements(&self) -> c_uint { self.ptrs.len() as c_uint }

  #[inline]
  pub(crate) fn exts_ptr(&self) -> Option<*const *const hs::hs_expr_ext> {
    self
      .exts
      .as_ref()
      .map(|e| unsafe { mem::transmute(e.as_ptr()) })
  }

  #[inline]
  pub(crate) fn expressions_ptr(&self) -> *const *const c_char { self.ptrs.as_ptr() }

  #[inline]
  pub(crate) fn flags_ptr(&self) -> *const c_uint {
    self
      .flags
      .as_ref()
      .map(|f| unsafe { mem::transmute(f.as_ptr()) })
      .unwrap_or(ptr::null())
  }

  #[inline]
  pub(crate) fn ids_ptr(&self) -> *const c_uint {
    self
      .ids
      .as_ref()
      .map(|i| unsafe { mem::transmute(i.as_ptr()) })
      .unwrap_or(ptr::null())
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct ExprExt(hs::hs_expr_ext);

impl Default for ExprExt {
  fn default() -> Self { Self::zeroed() }
}

impl ExprExt {
  #[inline]
  pub const fn zeroed() -> Self { unsafe { mem::MaybeUninit::zeroed().assume_init() } }

  #[inline]
  pub const fn from_min_offset(x: usize) -> Self {
    let ext_flags = ExtFlags::MIN_OFFSET;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.min_offset = x as c_ulonglong;
    s
  }

  #[inline]
  pub const fn from_max_offset(x: usize) -> Self {
    let ext_flags = ExtFlags::MAX_OFFSET;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.max_offset = x as c_ulonglong;
    s
  }

  #[inline]
  pub const fn from_min_length(x: usize) -> Self {
    let ext_flags = ExtFlags::MIN_LENGTH;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.min_length = x as c_ulonglong;
    s
  }

  #[inline]
  pub const fn from_edit_distance(x: usize) -> Self {
    let ext_flags = ExtFlags::EDIT_DISTANCE;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    assert!(x < c_uint::MAX as usize);
    s.0.edit_distance = x as c_uint;
    s
  }

  #[inline]
  pub const fn from_hamming_distance(x: usize) -> Self {
    let ext_flags = ExtFlags::HAMMING_DISTANCE;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    assert!(x < c_uint::MAX as usize);
    s.0.hamming_distance = x as c_uint;
    s
  }

  #[inline]
  fn ext_flags(&self) -> ExtFlags { ExtFlags::from_native(self.0.flags) }

  #[inline]
  pub fn min_offset(&self) -> Option<c_ulonglong> {
    if self.ext_flags().has_min_offset() {
      Some(self.0.min_offset)
    } else {
      None
    }
  }

  #[inline]
  pub fn max_offset(&self) -> Option<c_ulonglong> {
    if self.ext_flags().has_max_offset() {
      Some(self.0.max_offset)
    } else {
      None
    }
  }

  #[inline]
  pub fn min_length(&self) -> Option<c_ulonglong> {
    if self.ext_flags().has_min_length() {
      Some(self.0.min_length)
    } else {
      None
    }
  }

  #[inline]
  pub fn edit_distance(&self) -> Option<c_uint> {
    if self.ext_flags().has_edit_distance() {
      Some(self.0.edit_distance)
    } else {
      None
    }
  }

  #[inline]
  pub fn hamming_distance(&self) -> Option<c_uint> {
    if self.ext_flags().has_hamming_distance() {
      Some(self.0.hamming_distance)
    } else {
      None
    }
  }

  fn compose(mut self, rhs: Self) -> Self {
    self.0.flags = (self.ext_flags() | rhs.ext_flags()).into_native();
    if let Some(min_offset) = rhs.min_offset() {
      self.0.min_offset = min_offset;
    }
    if let Some(max_offset) = rhs.max_offset() {
      self.0.max_offset = max_offset;
    }
    if let Some(min_length) = rhs.min_length() {
      self.0.min_length = min_length;
    }
    if let Some(edit_distance) = rhs.edit_distance() {
      self.0.edit_distance = edit_distance;
    }
    if let Some(hamming_distance) = rhs.hamming_distance() {
      self.0.hamming_distance = hamming_distance;
    }
    self
  }
}

impl AsRef<hs::hs_expr_ext> for ExprExt {
  fn as_ref(&self) -> &hs::hs_expr_ext { &self.0 }
}

impl AsMut<hs::hs_expr_ext> for ExprExt {
  fn as_mut(&mut self) -> &mut hs::hs_expr_ext { &mut self.0 }
}

impl ops::BitOr for ExprExt {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { self.compose(other) }
}

impl ops::BitOrAssign for ExprExt {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

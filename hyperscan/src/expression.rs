/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  database::Database,
  error::{HyperscanCompileError, HyperscanRuntimeError},
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

///```
/// # fn main() -> Result<(), hyperscan_async::error::HyperscanError> {
/// use hyperscan_async::{expression::*, flags::Flags};
///
/// let expr: Expression = "(he)llo".parse()?;
/// let info = expr.info(Flags::default())?;
/// assert_eq!(info, ExprInfo {
///   min_width: ExprWidth::parse_min_width(0),
///   max_width: ExprWidth::parse_max_width(0),
///   unordered_matches: UnorderedMatchBehavior::OnlyOrdered,
///   matches_at_eod: MatchAtEndBehavior::NoMatchAtEOD,
/// });
/// let ext = ExprExt::from_min_length(2);
/// let info = expr.ext_info(Flags::default(), &ext)?;
/// assert_eq!(info, ExprInfo {
///   min_width: ExprWidth::parse_min_width(0),
///   max_width: ExprWidth::parse_max_width(0),
///   unordered_matches: UnorderedMatchBehavior::OnlyOrdered,
///   matches_at_eod: MatchAtEndBehavior::NoMatchAtEOD,
/// });
/// # Ok(())
/// # }
/// ```
#[derive(Clone)]
pub struct Expression(CString);

impl fmt::Debug for Expression {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let b = self.as_bytes();
    match str::from_utf8(b) {
      Ok(s) => write!(f, "Expression({:?})", s),
      Err(_) => write!(f, "Expression({:?})", b),
    }
  }
}

impl Expression {
  #[inline]
  pub fn as_bytes(&self) -> &[u8] { self.0.as_bytes() }

  #[inline]
  pub(crate) fn as_ptr(&self) -> *const c_char { self.0.as_c_str().as_ptr() }

  #[inline]
  pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, HyperscanCompileError> {
    Ok(Self(CString::new(x)?))
  }

  #[inline]
  pub fn info(&self, flags: Flags) -> Result<ExprInfo, HyperscanCompileError> {
    let mut info = mem::MaybeUninit::<hs::hs_expr_info>::zeroed();
    let mut compile_err = mem::MaybeUninit::<hs::hs_compile_error>::uninit();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_expression_info(
          self.as_ptr(),
          flags.into_native(),
          &mut info.as_mut_ptr() as *mut *mut hs::hs_expr_info,
          &mut compile_err.as_mut_ptr() as *mut *mut hs::hs_compile_error,
        )
      },
      compile_err.as_mut_ptr(),
    )?;
    let info = ExprInfo::from_native(unsafe { info.assume_init() });
    Ok(info)
  }

  #[inline]
  pub fn ext_info(
    &self,
    flags: Flags,
    ext_flags: &ExprExt,
  ) -> Result<ExprInfo, HyperscanCompileError> {
    let mut info = mem::MaybeUninit::<hs::hs_expr_info>::zeroed();
    let mut compile_err = mem::MaybeUninit::<hs::hs_compile_error>::uninit();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_expression_ext_info(
          self.as_ptr(),
          flags.into_native(),
          ext_flags.as_ref_native(),
          &mut info.as_mut_ptr() as *mut *mut hs::hs_expr_info,
          &mut compile_err.as_mut_ptr() as *mut *mut hs::hs_compile_error,
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

impl str::FromStr for Expression {
  type Err = HyperscanCompileError;

  fn from_str(s: &str) -> Result<Self, Self::Err> { Self::new(s) }
}

#[derive(Clone)]
pub struct Literal(Vec<u8>);

impl fmt::Debug for Literal {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let b = self.as_bytes();
    match str::from_utf8(b) {
      Ok(s) => write!(f, "Literal({:?})", s),
      Err(_) => write!(f, "Literal({:?})", b),
    }
  }
}

impl Literal {
  #[inline]
  pub fn as_bytes(&self) -> &[u8] { &self.0 }

  #[inline]
  pub(crate) fn as_ptr(&self) -> *const c_char {
    unsafe { mem::transmute(self.as_bytes().as_ptr()) }
  }

  #[inline]
  pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, HyperscanCompileError> { Ok(Self(x.into())) }

  pub fn compile(&self, flags: Flags, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_literal(self, flags, mode)
  }
}

impl str::FromStr for Literal {
  type Err = HyperscanCompileError;

  fn from_str(s: &str) -> Result<Self, Self::Err> { Self::new(s) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExprId(pub c_uint);

#[derive(Debug, Clone)]
pub struct ExpressionSet<'a> {
  ptrs: Vec<*const c_char>,
  flags: Option<Vec<Flags>>,
  ids: Option<Vec<ExprId>>,
  exts: Option<Vec<*const hs::hs_expr_ext>>,
  _ph: PhantomData<&'a u8>,
}

impl<'a> ExpressionSet<'a> {
  pub fn from_exprs(exprs: impl IntoIterator<Item=&'a Expression>) -> Self {
    Self {
      ptrs: exprs.into_iter().map(|e| e.as_ptr()).collect(),
      flags: None,
      ids: None,
      exts: None,
      _ph: PhantomData,
    }
  }

  pub fn with_flags(mut self, flags: impl IntoIterator<Item=Flags>) -> Self {
    let flags: Vec<_> = flags.into_iter().collect();
    assert_eq!(self.ptrs.len(), flags.len());
    self.flags = Some(flags);
    self
  }

  pub fn with_ids(mut self, ids: impl IntoIterator<Item=ExprId>) -> Self {
    let ids: Vec<_> = ids.into_iter().collect();
    assert_eq!(self.ptrs.len(), ids.len());
    self.ids = Some(ids);
    self
  }

  pub fn with_exts(mut self, exts: impl IntoIterator<Item=Option<&'a ExprExt>>) -> Self {
    let exts: Vec<*const hs::hs_expr_ext> = exts
      .into_iter()
      .map(|e| {
        e.map(|e| e.as_ref_native() as *const hs::hs_expr_ext)
          .unwrap_or(ptr::null())
      })
      .collect();
    assert_eq!(self.ptrs.len(), exts.len());
    self.exts = Some(exts);
    self
  }

  pub fn compile(self, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_multi(&self, mode)
  }

  #[inline]
  pub(crate) fn num_elements(&self) -> c_uint { self.ptrs.len() as c_uint }

  #[inline]
  pub(crate) fn exts_ptr(&self) -> Option<*const *const hs::hs_expr_ext> {
    self.exts.as_ref().map(|e| e.as_ptr())
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
  pub fn zeroed() -> Self { unsafe { mem::MaybeUninit::zeroed().assume_init() } }

  #[inline]
  pub fn from_min_offset(x: usize) -> Self {
    let ext_flags = ExtFlags::MIN_OFFSET;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.min_offset = x as c_ulonglong;
    s
  }

  #[inline]
  pub fn from_max_offset(x: usize) -> Self {
    let ext_flags = ExtFlags::MAX_OFFSET;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.max_offset = x as c_ulonglong;
    s
  }

  #[inline]
  pub fn from_min_length(x: usize) -> Self {
    let ext_flags = ExtFlags::MIN_LENGTH;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.min_length = x as c_ulonglong;
    s
  }

  #[inline]
  pub fn from_edit_distance(x: usize) -> Self {
    let ext_flags = ExtFlags::EDIT_DISTANCE;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    assert!(x < c_uint::MAX as usize);
    s.0.edit_distance = x as c_uint;
    s
  }

  #[inline]
  pub fn from_hamming_distance(x: usize) -> Self {
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

  #[inline]
  pub(crate) fn as_ref_native(&self) -> &hs::hs_expr_ext { &self.0 }
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

#[derive(Debug, Clone)]
pub struct LiteralSet<'a> {
  ptrs: Vec<*const c_char>,
  lens: Vec<usize>,
  flags: Option<Vec<Flags>>,
  ids: Option<Vec<ExprId>>,
  _ph: PhantomData<&'a u8>,
}

impl<'a> LiteralSet<'a> {
  pub fn from_lits(lits: impl IntoIterator<Item=&'a Literal>) -> Self {
    let mut ptrs: Vec<_> = Vec::new();
    let mut lens: Vec<_> = Vec::new();

    for l in lits.into_iter() {
      ptrs.push(l.as_ptr());
      lens.push(l.as_bytes().len());
    }

    Self {
      ptrs,
      lens,
      flags: None,
      ids: None,
      _ph: PhantomData,
    }
  }

  pub fn with_flags(mut self, flags: impl IntoIterator<Item=Flags>) -> Self {
    let flags: Vec<_> = flags.into_iter().collect();
    assert_eq!(self.ptrs.len(), flags.len());
    self.flags = Some(flags.to_vec());
    self
  }

  pub fn with_ids(mut self, ids: impl IntoIterator<Item=ExprId>) -> Self {
    let ids: Vec<_> = ids.into_iter().collect();
    assert_eq!(self.ptrs.len(), ids.len());
    self.ids = Some(ids.to_vec());
    self
  }

  pub fn compile(self, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_multi_literal(&self, mode)
  }

  #[inline]
  pub(crate) fn num_elements(&self) -> c_uint { self.ptrs.len() as c_uint }

  #[inline]
  pub(crate) fn literals_ptr(&self) -> *const *const c_char { self.ptrs.as_ptr() }

  #[inline]
  pub(crate) fn lengths_ptr(&self) -> *const usize { self.lens.as_ptr() }

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

#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::ExprId;
  use crate::{
    database::chimera::ChimeraDb,
    error::chimera::ChimeraCompileError,
    flags::chimera::{ChimeraFlags, ChimeraMode},
  };

  use std::{
    ffi::CString,
    fmt,
    marker::PhantomData,
    mem,
    os::raw::{c_char, c_uint, c_ulong},
    ptr, str,
  };

  #[derive(Clone)]
  pub struct ChimeraExpression(CString);

  impl fmt::Debug for ChimeraExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      let b = self.as_bytes();
      match str::from_utf8(b) {
        Ok(s) => write!(f, "ChimeraExpression({:?})", s),
        Err(_) => write!(f, "ChimeraExpression({:?})", b),
      }
    }
  }

  impl ChimeraExpression {
    #[inline]
    pub fn as_bytes(&self) -> &[u8] { self.0.as_bytes() }

    #[inline]
    pub(crate) fn as_ptr(&self) -> *const c_char { self.0.as_c_str().as_ptr() }

    #[inline]
    pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, ChimeraCompileError> {
      Ok(Self(CString::new(x)?))
    }

    pub fn compile(
      &self,
      flags: ChimeraFlags,
      mode: ChimeraMode,
    ) -> Result<ChimeraDb, ChimeraCompileError> {
      ChimeraDb::compile(self, flags, mode)
    }
  }

  impl str::FromStr for ChimeraExpression {
    type Err = ChimeraCompileError;

    fn from_str(s: &str) -> Result<Self, Self::Err> { Self::new(s) }
  }

  #[derive(Debug, Copy, Clone)]
  pub struct ChimeraMatchLimits {
    /// A limit from pcre_extra on the amount of match function called in PCRE
    /// to limit backtracking that can take place.
    pub match_limit: c_ulong,
    /// A limit from pcre_extra on the recursion depth of match function in
    /// PCRE.
    pub match_limit_recursion: c_ulong,
  }

  #[derive(Debug, Clone)]
  pub struct ChimeraExpressionSet<'a> {
    ptrs: Vec<*const c_char>,
    flags: Option<Vec<ChimeraFlags>>,
    ids: Option<Vec<ExprId>>,
    limits: Option<ChimeraMatchLimits>,
    _ph: PhantomData<&'a u8>,
  }

  impl<'a> ChimeraExpressionSet<'a> {
    pub fn from_exprs(exprs: impl IntoIterator<Item=&'a ChimeraExpression>) -> Self {
      Self {
        ptrs: exprs.into_iter().map(|e| e.as_ptr()).collect(),
        flags: None,
        ids: None,
        limits: None,
        _ph: PhantomData,
      }
    }

    pub fn with_flags(mut self, flags: impl IntoIterator<Item=ChimeraFlags>) -> Self {
      let flags: Vec<_> = flags.into_iter().collect();
      assert_eq!(self.ptrs.len(), flags.len());
      self.flags = Some(flags);
      self
    }

    pub fn with_ids(mut self, ids: impl IntoIterator<Item=ExprId>) -> Self {
      let ids: Vec<_> = ids.into_iter().collect();
      assert_eq!(self.ptrs.len(), ids.len());
      self.ids = Some(ids);
      self
    }

    pub fn with_limits(mut self, limits: ChimeraMatchLimits) -> Self {
      self.limits = Some(limits);
      self
    }

    pub fn compile(self, mode: ChimeraMode) -> Result<ChimeraDb, ChimeraCompileError> {
      ChimeraDb::compile_multi(&self, mode)
    }

    #[inline]
    pub(crate) fn limits(&self) -> Option<ChimeraMatchLimits> { self.limits }

    #[inline]
    pub(crate) fn num_elements(&self) -> c_uint { self.ptrs.len() as c_uint }

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
}

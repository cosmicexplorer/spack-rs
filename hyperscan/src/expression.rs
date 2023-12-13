/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! FFI wrappers for different types of pattern strings.
//!
//! Hyperscan supports 3 distinct types of pattern strings which can be formed
//! to produce a database:
//! - [`Expression`]: Hyperscan PCRE-like regex syntax (null-terminated
//!   [`CString`]).
//! - [`Literal`]: Literal byte string (`Vec<u8>`) which may contain nulls.
//! - [`chimera::ChimeraExpression`]: PCRE regex syntax.
//!
//! Each hyperscan database only supports matching against *exactly one* type of
//! these patterns, but each variant also has a `*Set` form, and all of these
//! forms support the same interface to hyperscan's most powerful feature:
//! multi-pattern matching, where patterns registered with [`ExprId`] in a set
//! can be associated to [`ExpressionIndex`](crate::matchers::ExpressionIndex)
//! instances when matched against.
//!
//! Creating instances of these structs performs no pattern compilation itself,
//! which is instead performed in a subsequent step by e.g.
//! [`Database::compile()`]. References to these structs can be reused multiple
//! times to create multiple databases without re-allocating the underlying
//! pattern string data:
//!
//!```
//! # #[allow(unused_variables)]
//! # fn main() -> Result<(), hyperscan::error::HyperscanError> {
//! use hyperscan::{expression::*, flags::*};
//!
//! let a: Expression = "a+".parse()?;
//! let b: Expression = "b+".parse()?;
//! let c: Expression = "c+".parse()?;
//!
//! let ab_db = ExpressionSet::from_exprs([&a, &b]).compile(Mode::BLOCK)?;
//! let bc_db = ExpressionSet::from_exprs([&b, &c]).compile(Mode::BLOCK)?;
//! let ca_db = ExpressionSet::from_exprs([&c, &a]).compile(Mode::BLOCK)?;
//! # Ok(())
//! # }
//! ```

use crate::{
  database::{Database, Platform},
  error::{HyperscanCompileError, HyperscanRuntimeError},
  flags::{ExtFlags, Flags, Mode},
  hs,
};

use displaydoc::Display;
use itertools::Itertools;

use std::{
  ffi::{CStr, CString},
  fmt,
  marker::PhantomData,
  mem, ops,
  os::raw::{c_char, c_uint, c_ulonglong},
  ptr, slice, str,
};

/// Hyperscan regex pattern string.
///
/// Hyperscan itself supports a subset of PCRE syntax in the pattern string; see
/// [Pattern Support] for reference. The use of unsupported constructs will
/// result in compilation errors.
///
/// Note that as the underlying hyperscan library interprets pattern strings as
/// essentially null-terminated [`CStr`] pointers, null bytes
/// are *not* supported within `Expression` strings. Use a [`Literal`] or
/// [`LiteralSet`] database if you need to match against patterns with null
/// bytes.
///
/// Instances can be created equivalently with [`Self::new()`] or
/// [`str::parse()`] via the [`str::FromStr`] impl:
///
///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
/// use hyperscan::expression::Expression;
///
/// let e1: Expression = "asdf+".parse()?;
/// let e2 = Expression::new("asdf+")?;
/// assert_eq!(e1, e2);
/// # Ok(())
/// # }
/// ```
///
/// [Pattern Support]: https://intel.github.io/hyperscan/dev-reference/compilation.html#pattern-support
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Expression(CString);

impl fmt::Display for Expression {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let b = self.as_bytes();
    match str::from_utf8(b) {
      Ok(s) => write!(f, "{}", s),
      Err(_) => write!(f, "(non-utf8: {:?})", b),
    }
  }
}

impl Expression {
  /// Reference the underlying bytes, *without* the trailing null terminator.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// let e = hyperscan::expression::Expression::new("asdf")?;
  /// assert_eq!(e.as_bytes(), b"asdf");
  /// # Ok(())
  /// # }
  /// ```
  pub fn as_bytes(&self) -> &[u8] { self.0.as_bytes() }

  pub(crate) fn as_ptr(&self) -> *const c_char { self.0.as_c_str().as_ptr() }

  /// Produce a `NULL`-terminated C-style wrapper for the given pattern string.
  ///
  /// This will fail if the string contains any internal `NULL` bytes, as those
  /// are not supported by the hyperscan regex compiler:
  ///```
  /// use hyperscan::{expression::*, error::*};
  ///
  /// let pat = "as\0df";
  /// let e = match Expression::new(pat) {
  ///    Err(HyperscanCompileError::NullByte(e)) => e,
  ///    _ => unreachable!(),
  /// };
  /// assert_eq!(e.nul_position(), 2);
  /// ```
  pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, HyperscanCompileError> {
    Ok(Self(CString::new(x)?))
  }

  /// Utility function providing information about a regular expression. The
  /// information provided in [`ExprInfo`] includes the minimum and
  /// maximum width of a pattern match.
  ///
  /// Note: successful analysis of an expression with this function does not
  /// imply that compilation of the same expression (via
  /// [`Database::compile()`] or [`Database::compile_multi()`]) would succeed.
  /// This function may return [`Ok`] for regular expressions that
  /// Hyperscan cannot compile.
  ///
  /// Note: some per-pattern flags (such as [`Flags::ALLOWEMPTY`] and
  /// [`Flags::SOM_LEFTMOST`]) are accepted by this call, but as they do not
  /// affect the properties returned in the [`ExprInfo`] structure,
  /// they will not affect the outcome of this function.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::Flags};
  ///
  /// let expr: Expression = "(he)llo".parse()?;
  ///
  /// let info = expr.info(Flags::default())?;
  ///
  /// assert_eq!(info, ExprInfo {
  ///   min_width: ExprWidth::parse_min_width(5),
  ///   max_width: ExprWidth::parse_max_width(5),
  ///   unordered_matches: UnorderedMatchBehavior::OnlyOrdered,
  ///   matches_at_eod: MatchAtEndBehavior::WillNeverMatchAtEOD,
  /// });
  /// # Ok(())
  /// # }
  /// ```
  pub fn info(&self, flags: Flags) -> Result<ExprInfo, HyperscanCompileError> {
    let mut info = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_expression_info(
          self.as_ptr(),
          flags.into_native(),
          &mut info,
          &mut compile_err,
        )
      },
      compile_err,
    )?;

    let ret = ExprInfo::from_native(unsafe { *info });

    unsafe {
      crate::free_misc(info as *mut u8);
    }

    Ok(ret)
  }

  /// Utility function providing information about a regular expression, with
  /// extended parameter support. The information provided in [`ExprInfo`]
  /// includes the minimum and maximum width of a pattern match.
  ///
  /// Note: successful analysis of an expression with this function does not
  /// imply that compilation of the same expression (via
  /// [`Database::compile()`] or [`Database::compile_multi()`]) would succeed.
  /// This function may return [`Ok`] for regular expressions that
  /// Hyperscan cannot compile.
  ///
  /// Note: some per-pattern flags (such as [`Flags::ALLOWEMPTY`] and
  /// [`Flags::SOM_LEFTMOST`]) are accepted by this call, but as they do not
  /// affect the properties returned in the [`ExprInfo`] structure,
  /// they will not affect the outcome of this function.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::Flags};
  ///
  /// let expr: Expression = ".*lo".parse()?;
  ///
  /// let ext = ExprExt::from_min_length(4);
  ///
  /// let info = expr.ext_info(Flags::default(), &ext)?;
  ///
  /// assert_eq!(info, ExprInfo {
  ///   min_width: ExprWidth::parse_min_width(4),
  ///   max_width: None,
  ///   unordered_matches: UnorderedMatchBehavior::OnlyOrdered,
  ///   matches_at_eod: MatchAtEndBehavior::WillNeverMatchAtEOD,
  /// });
  /// # Ok(())
  /// # }
  /// ```
  pub fn ext_info(
    &self,
    flags: Flags,
    ext_flags: &ExprExt,
  ) -> Result<ExprInfo, HyperscanCompileError> {
    let mut info = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_expression_ext_info(
          self.as_ptr(),
          flags.into_native(),
          ext_flags.as_ref_native(),
          &mut info,
          &mut compile_err,
        )
      },
      compile_err,
    )?;

    let ret = ExprInfo::from_native(unsafe { *info });

    unsafe {
      crate::free_misc(info as *mut u8);
    }

    Ok(ret)
  }

  /// Call [`Database::compile()`] with the result of [`Platform::get()`].
  pub fn compile(&self, flags: Flags, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile(self, flags, mode, Platform::get())
  }
}

impl str::FromStr for Expression {
  type Err = HyperscanCompileError;

  fn from_str(s: &str) -> Result<Self, Self::Err> { Self::new(s) }
}

/// A literal byte string.
///
/// Unlike for [`Expression`], [`Database::compile_literal()`] will parse the
/// string content in a literal sense without any regular grammars. For example,
/// the expression `abc?` simply means a char sequence of `a`, `b`, `c`,
/// and `?`. The `?` here doesn't mean 0 or 1 quantifier under regular
/// semantics.
///
/// Also unlike [`Expression`], the underlying hyperscan library interprets
/// literal patterns with a pointer and a length instead of a `NULL`-terminated
/// string. **Importantly, this allows it to contain `\0` or `NULL` bytes
/// itself!**
///
/// Instances can be created equivalently with [`Self::new()`] or
/// [`str::parse()`] via the [`str::FromStr`] impl:
///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
/// use hyperscan::expression::Literal;
///
/// let e1: Literal = "as\0df".parse()?;
/// let e2 = Literal::new("as\0df")?;
/// assert_eq!(e1, e2);
/// # Ok(())
/// # }
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl fmt::Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let b = self.as_bytes();
    match str::from_utf8(b) {
      Ok(s) => write!(f, "{}", s),
      Err(_) => write!(f, "(non-utf8 literal: {:?})", b),
    }
  }
}

impl Literal {
  /// Reference the underlying bytes. This wrapper does *not* allocate any null
  /// terminator.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// let e = hyperscan::expression::Literal::new("as\0df")?;
  /// assert_eq!(e.as_bytes(), b"as\0df");
  /// # Ok(())
  /// # }
  /// ```
  pub fn as_bytes(&self) -> &[u8] { &self.0 }

  pub(crate) fn as_ptr(&self) -> *const c_char {
    unsafe { mem::transmute(self.as_bytes().as_ptr()) }
  }

  /// Wrap a byte slice to be interpreted literally. This does *not* allocate
  /// any null terminator.
  pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, HyperscanCompileError> { Ok(Self(x.into())) }

  /// Call [`Database::compile_literal()`] with the result of
  /// [`Platform::get()`].
  pub fn compile(&self, flags: Flags, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_literal(self, flags, mode, Platform::get())
  }
}

impl str::FromStr for Literal {
  type Err = HyperscanCompileError;

  fn from_str(s: &str) -> Result<Self, Self::Err> { Self::new(s) }
}

/// The ID number to associate with a pattern match in an expression set.
///
/// When provided to an expression set, this value is converted into an
/// [`ExpressionIndex`](crate::matchers::ExpressionIndex) in a
/// [`Match`](crate::matchers::contiguous_slice::Match),
/// [`VectoredMatch`](crate::matchers::vectored_slice::VectoredMatch), or
/// [`ChimeraMatch`](crate::matchers::chimera::ChimeraMatch) upon matching the
/// given pattern.
///
/// This ID is used in [`ExpressionSet::with_ids()`],
/// [`LiteralSet::with_ids()`], and
/// [`ChimeraExpressionSet::with_ids()`](chimera::ChimeraExpressionSet::with_ids).
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExprId(pub c_uint);

/// Collection of regular expressions.
///
/// This is the main entry point to hyperscan's primary functionality: matching
/// against sets of patterns at once, which is typically poorly supported or
/// less featureful than single-pattern matching in many other regex engines.
///
/// This struct provides an immutable (returning `Self`) builder interface
/// to attach additional configuration to the initial set of patterns
/// constructed with [`Self::from_exprs()`].
#[derive(Clone)]
pub struct ExpressionSet<'a> {
  ptrs: Vec<*const c_char>,
  flags: Option<Vec<Flags>>,
  ids: Option<Vec<ExprId>>,
  exts: Option<Vec<*const hs::hs_expr_ext>>,
  _ph: PhantomData<&'a u8>,
}

impl<'a> fmt::Debug for ExpressionSet<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let exprs: Vec<&'a CStr> = self
      .ptrs
      .iter()
      .map(|p| unsafe { CStr::from_ptr(*p) })
      .collect();
    let exts: Option<&[Option<&ExprExt>]> = self
      .exts
      .as_ref()
      .map(|exts| unsafe { slice::from_raw_parts(mem::transmute(exts.as_ptr()), exprs.len()) });
    write!(
      f,
      "ExpressionSet(exprs={:?}, flags={:?}, ids={:?}, exts={:?})",
      exprs, &self.flags, &self.ids, exts,
    )
  }
}

impl<'a> ExpressionSet<'a> {
  /// Construct a pattern set from references to parsed expressions.
  ///
  /// The length of this initial `exprs` argument is returned by
  /// [`Self::len()`], and all subsequent configuration methods are checked to
  /// provide iterators of the same length:
  ///
  ///```should_panic
  /// use hyperscan::expression::*;
  ///
  /// let a: Expression = "a+".parse().unwrap();
  /// // Fails due to argument length mismatch:
  /// ExpressionSet::from_exprs([&a])
  ///   .with_flags([]);
  /// ```
  pub fn from_exprs(exprs: impl IntoIterator<Item=&'a Expression>) -> Self {
    Self {
      ptrs: exprs.into_iter().map(|e| e.as_ptr()).collect(),
      flags: None,
      ids: None,
      exts: None,
      _ph: PhantomData,
    }
  }

  /// Provide flags which modify the behavior of each expression.
  ///
  /// The length of `flags` is checked to be the same as [`Self::len()`].
  ///
  /// If this builder method is not used, [`Flags::default()`] will be assigned
  /// to all patterns.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, matchers::*};
  ///
  /// // Create two expressions to demonstrate separate flags for each pattern:
  /// let a: Expression = "a+[^a]".parse()?;
  /// let b: Expression = "b+[^b]".parse()?;
  ///
  /// // Get the start of match for one pattern, but not the other:
  /// let db = ExpressionSet::from_exprs([&a, &b])
  ///   .with_flags([Flags::default(), Flags::SOM_LEFTMOST])
  ///   .compile(Mode::BLOCK)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// scratch.scan_sync(&db, "aardvark imbibbe".into(), |m| {
  ///   matches.push(unsafe { m.source.as_str() });
  ///   MatchResult::Continue
  /// })?;
  /// // Start of match is preserved for only one pattern:
  /// assert_eq!(&matches, &["aar", "aardvar", "bi", "bbe"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn with_flags(mut self, flags: impl IntoIterator<Item=Flags>) -> Self {
    let flags: Vec<_> = flags.into_iter().collect();
    assert_eq!(self.len(), flags.len());
    self.flags = Some(flags);
    self
  }

  /// Assign an ID number to each pattern.
  ///
  /// The length of `ids` is checked to be the same as [`Self::len()`]. Multiple
  /// patterns can be assigned the same ID.
  ///
  /// If this builder method is not used, hyperscan will assign them all the ID
  /// number 0:
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, state::*, matchers::*};
  ///
  /// // Create two expressions to demonstrate multiple pattern IDs.
  /// let a: Expression = "a+[^a]".parse()?;
  /// let b: Expression = "b+[^b]".parse()?;
  ///
  /// // Create one db with ID numbers, and one without.
  /// let set1 = ExpressionSet::from_exprs([&a, &b]).compile(Mode::BLOCK)?;
  /// let set2 = ExpressionSet::from_exprs([&a, &b])
  ///   .with_ids([ExprId(300), ExprId(12)])
  ///   .compile(Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::new();
  /// scratch.setup_for_db(&set1)?;
  /// scratch.setup_for_db(&set2)?;
  ///
  /// let msg: ByteSlice = "aardvark imbibbe".into();
  ///
  /// // The first db doesn't differentiate matches by ID number:
  /// let mut matches1: Vec<ExpressionIndex> = Vec::new();
  /// scratch.scan_sync(&set1, msg, |m| {
  ///   matches1.push(m.id);
  ///   MatchResult::Continue
  /// })?;
  /// assert_eq!(
  ///   &matches1,
  ///   &[ExpressionIndex(0), ExpressionIndex(0), ExpressionIndex(0), ExpressionIndex(0)],
  /// );
  ///
  /// // The second db returns corresponding ExpressionIndex instances:
  /// let mut matches2: Vec<ExpressionIndex> = Vec::new();
  /// scratch.scan_sync(&set2, msg, |m| {
  ///   matches2.push(m.id);
  ///   MatchResult::Continue
  /// })?;
  /// assert_eq!(
  ///   &matches2,
  ///   &[ExpressionIndex(300), ExpressionIndex(300), ExpressionIndex(12), ExpressionIndex(12)],
  /// );
  /// # Ok(())
  /// # }
  /// ```
  pub fn with_ids(mut self, ids: impl IntoIterator<Item=ExprId>) -> Self {
    let ids: Vec<_> = ids.into_iter().collect();
    assert_eq!(self.len(), ids.len());
    self.ids = Some(ids);
    self
  }

  /// Optionally assign [`ExprExt`] configuration to each pattern.
  ///
  /// This is the only available entry point to compiling a database with
  /// [`ExprExt`] configuration for a given pattern (i.e. the single
  /// expression compiler does not support extended configuration).
  ///
  /// If [`Expression::ext_info()`] succeeds with a given
  /// [`Expression`]/[`ExprExt`] pair, then compiling the same pattern and
  /// configuration into a hyperscan database via an expression set with this
  /// method is likely but not guaranteed to succeed.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, matchers::*};
  ///
  /// // Apply extended configuration to one pattern, but not the other:
  /// let a: Expression = "a.*b".parse()?;
  /// let a_ext = ExprExt::from_min_length(4);
  /// let set = ExpressionSet::from_exprs([&a, &a])
  ///   .with_exts([Some(&a_ext), None])
  ///   .with_ids([ExprId(1), ExprId(2)])
  ///   .compile(Mode::BLOCK)?;
  /// let mut scratch = set.allocate_scratch()?;
  ///
  /// // The configured pattern does not match because of its min length attribute:
  /// let mut matches: Vec<ExpressionIndex> = Vec::new();
  /// scratch.scan_sync(&set, "ab".into(), |m| {
  ///   matches.push(m.id);
  ///   MatchResult::Continue
  /// })?;
  /// assert_eq!(&matches, &[ExpressionIndex(2)]);
  ///
  /// // Howver, both patterns match a longer input:
  /// matches.clear();
  /// scratch.scan_sync(&set, "asssssb".into(), |m| {
  ///   matches.push(m.id);
  ///   MatchResult::Continue
  /// })?;
  /// assert_eq!(&matches, &[ExpressionIndex(1), ExpressionIndex(2)]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn with_exts(mut self, exts: impl IntoIterator<Item=Option<&'a ExprExt>>) -> Self {
    let exts: Vec<*const hs::hs_expr_ext> = exts
      .into_iter()
      .map(|e| {
        e.map(|e| e.as_ref_native() as *const hs::hs_expr_ext)
          .unwrap_or(ptr::null())
      })
      .collect();
    assert_eq!(self.len(), exts.len());
    self.exts = Some(exts);
    self
  }

  /// Call [`Database::compile_multi()`] with the result of [`Platform::get()`].
  pub fn compile(self, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_multi(&self, mode, Platform::get())
  }

  /// The number of patterns in this set.
  pub fn len(&self) -> usize { self.ptrs.len() }

  /// Whether this set contains any patterns.
  pub fn is_empty(&self) -> bool { self.len() == 0 }

  pub(crate) fn num_elements(&self) -> c_uint { self.len() as c_uint }

  pub(crate) fn exts_ptr(&self) -> Option<*const *const hs::hs_expr_ext> {
    self.exts.as_ref().map(|e| e.as_ptr())
  }

  pub(crate) fn expressions_ptr(&self) -> *const *const c_char { self.ptrs.as_ptr() }

  pub(crate) fn flags_ptr(&self) -> *const c_uint {
    self
      .flags
      .as_ref()
      .map(|f| unsafe { mem::transmute(f.as_ptr()) })
      .unwrap_or(ptr::null())
  }

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
  pub const fn parse_min_width(x: c_uint) -> Self { Self(x as usize) }

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
  /// Disallows matches that are not returned in order.
  #[num_enum(default)]
  OnlyOrdered = 0,
  /// Allows matches that are not returned in order.
  AllowsUnordered = 1,
}

impl UnorderedMatchBehavior {
  pub const fn from_native(x: c_char) -> Self {
    if x == 0 {
      Self::OnlyOrdered
    } else {
      Self::AllowsUnordered
    }
  }
}

#[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(i8)]
pub enum MatchAtEndBehavior {
  /// Pattern will never match at EOD.
  WillNeverMatchAtEOD,
  /// Pattern may match at EOD.
  MayMatchAtEOD,
  /// Pattern will *Only* match at EOD.
  WillOnlyMatchAtEOD,
}

impl MatchAtEndBehavior {
  pub fn from_native(matches_at_eod: c_char, matches_only_at_eod: c_char) -> Self {
    match (matches_at_eod, matches_only_at_eod) {
      (0, 0) => Self::WillNeverMatchAtEOD,
      (x, 0) if x != 0 => Self::MayMatchAtEOD,
      (_, x) if x != 0 => Self::WillOnlyMatchAtEOD,
      x => unreachable!("unreachable pattern: {:?}", x),
    }
  }
}

///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
/// use hyperscan::{expression::*, flags::Flags};
///
/// let expr: Expression = "(he)llo$".parse()?;
/// let info = expr.info(Flags::default())?;
/// assert_eq!(info, ExprInfo {
///   min_width: ExprWidth::parse_min_width(5),
///   max_width: ExprWidth::parse_max_width(5),
///   unordered_matches: UnorderedMatchBehavior::AllowsUnordered,
///   matches_at_eod: MatchAtEndBehavior::WillOnlyMatchAtEOD,
/// });
/// # Ok(())
/// # }
/// ```
///
///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
/// use hyperscan::{expression::*, flags::Flags};
///
/// let expr: Expression = ".*lo($)?".parse()?;
/// let ext = ExprExt::from_min_length(4);
/// let info = expr.ext_info(Flags::default(), &ext)?;
/// assert_eq!(info, ExprInfo {
///   min_width: ExprWidth::parse_min_width(4),
///   max_width: None,
///   unordered_matches: UnorderedMatchBehavior::AllowsUnordered,
///   matches_at_eod: MatchAtEndBehavior::MayMatchAtEOD,
/// });
/// # Ok(())
/// # }
/// ```
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
  pub(crate) fn from_native(x: hs::hs_expr_info) -> Self {
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
  pub fn zeroed() -> Self { unsafe { mem::MaybeUninit::zeroed().assume_init() } }

  pub fn from_min_offset(x: usize) -> Self {
    let ext_flags = ExtFlags::MIN_OFFSET;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.min_offset = x as c_ulonglong;
    s
  }

  pub fn from_max_offset(x: usize) -> Self {
    let ext_flags = ExtFlags::MAX_OFFSET;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.max_offset = x as c_ulonglong;
    s
  }

  pub fn from_min_length(x: usize) -> Self {
    let ext_flags = ExtFlags::MIN_LENGTH;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    s.0.min_length = x as c_ulonglong;
    s
  }

  pub fn from_edit_distance(x: usize) -> Self {
    let ext_flags = ExtFlags::EDIT_DISTANCE;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    assert!(x < c_uint::MAX as usize);
    s.0.edit_distance = x as c_uint;
    s
  }

  pub fn from_hamming_distance(x: usize) -> Self {
    let ext_flags = ExtFlags::HAMMING_DISTANCE;
    let mut s = Self::zeroed();
    s.0.flags = ext_flags.into_native();
    assert!(x < c_uint::MAX as usize);
    s.0.hamming_distance = x as c_uint;
    s
  }

  fn ext_flags(&self) -> ExtFlags { ExtFlags::from_native(self.0.flags) }

  pub fn min_offset(&self) -> Option<c_ulonglong> {
    if self.ext_flags().has_min_offset() {
      Some(self.0.min_offset)
    } else {
      None
    }
  }

  pub fn max_offset(&self) -> Option<c_ulonglong> {
    if self.ext_flags().has_max_offset() {
      Some(self.0.max_offset)
    } else {
      None
    }
  }

  pub fn min_length(&self) -> Option<c_ulonglong> {
    if self.ext_flags().has_min_length() {
      Some(self.0.min_length)
    } else {
      None
    }
  }

  pub fn edit_distance(&self) -> Option<c_uint> {
    if self.ext_flags().has_edit_distance() {
      Some(self.0.edit_distance)
    } else {
      None
    }
  }

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

/// Collection of literals.
///
/// This is the analogue to [`ExpressionSet`] for [`Literal`] expressions, which
/// cannot be combined with [`Expression`] patterns in the same database.
///
/// This struct provides an immutable (returning `Self`) builder interface
/// to attach additional configuration to the initial set of patterns
/// constructed with [`Self::from_lits()`].
#[derive(Clone)]
pub struct LiteralSet<'a> {
  ptrs: Vec<*const c_char>,
  lens: Vec<usize>,
  flags: Option<Vec<Flags>>,
  ids: Option<Vec<ExprId>>,
  _ph: PhantomData<&'a u8>,
}

impl<'a> fmt::Debug for LiteralSet<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let exprs: Vec<&'a [u8]> = self
      .ptrs
      .iter()
      .zip(self.lens.iter())
      .map(|(p, n)| unsafe { slice::from_raw_parts(*p as *const u8, *n) })
      .collect();
    let joined_exprs: String = exprs
      .into_iter()
      .map(|s| {
        str::from_utf8(s)
          .map(|s| format!("{:?}", s))
          .unwrap_or_else(|_| format!("(non-utf8: {:?})", s))
      })
      .join(", ");
    write!(
      f,
      "LiteralSet(exprs=[{}], flags={:?}, ids={:?})",
      joined_exprs, &self.flags, &self.ids
    )
  }
}

impl<'a> LiteralSet<'a> {
  /// Construct a pattern set from references to parsed literals.
  ///
  /// The length of this initial `exprs` argument is returned by
  /// [`Self::len()`], and all subsequent configuration methods are checked to
  /// provide iterators of the same length:
  ///
  ///```should_panic
  /// use hyperscan::expression::*;
  ///
  /// let a: Literal = "a\0b".parse().unwrap();
  /// // Fails due to argument length mismatch:
  /// LiteralSet::from_lits([&a])
  ///   .with_flags([]);
  /// ```
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

  /// Provide flags which modify the behavior of each expression.
  ///
  /// The length of `flags` is checked to be the same as [`Self::len()`].
  ///
  /// If this builder method is not used, [`Flags::default()`] will be assigned
  /// to all patterns.
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, matchers::*};
  ///
  /// // Create two expressions to demonstrate separate flags for each pattern:
  /// let a: Literal = "a".parse()?;
  /// let b: Literal = "b".parse()?;
  ///
  /// // Get the start of match for one pattern, but not the other:
  /// let db = LiteralSet::from_lits([&a, &b])
  ///   .with_flags([Flags::default(), Flags::SOM_LEFTMOST])
  ///   .compile(Mode::BLOCK)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// scratch.scan_sync(&db, "aardvark imbibbe".into(), |m| {
  ///   matches.push(unsafe { m.source.as_str() });
  ///   MatchResult::Continue
  /// })?;
  /// // Start of match is preserved for only one pattern:
  /// assert_eq!(&matches, &["a", "aa", "aardva", "b", "b", "b"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn with_flags(mut self, flags: impl IntoIterator<Item=Flags>) -> Self {
    let flags: Vec<_> = flags.into_iter().collect();
    assert_eq!(self.len(), flags.len());
    self.flags = Some(flags.to_vec());
    self
  }

  /// Assign an ID number to each pattern.
  ///
  /// The length of `ids` is checked to be the same as [`Self::len()`]. Multiple
  /// patterns can be assigned the same ID.
  ///
  /// If this builder method is not used, hyperscan will assign them all the ID
  /// number 0:
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, state::*, matchers::*};
  ///
  /// // Create two expressions to demonstrate multiple pattern IDs.
  /// let a: Literal = "a".parse()?;
  /// let b: Literal = "b".parse()?;
  ///
  /// // Create one db with ID numbers, and one without.
  /// let set1 = LiteralSet::from_lits([&a, &b]).compile(Mode::BLOCK)?;
  /// let set2 = LiteralSet::from_lits([&a, &b])
  ///   .with_ids([ExprId(300), ExprId(12)])
  ///   .compile(Mode::BLOCK)?;
  ///
  /// let mut scratch = Scratch::new();
  /// scratch.setup_for_db(&set1)?;
  /// scratch.setup_for_db(&set2)?;
  ///
  /// let msg: ByteSlice = "aardvark imbibbe".into();
  ///
  /// // The first db doesn't differentiate matches by ID number:
  /// let mut matches1: Vec<ExpressionIndex> = Vec::new();
  /// scratch.scan_sync(&set1, msg, |m| {
  ///   matches1.push(m.id);
  ///   MatchResult::Continue
  /// })?;
  /// assert_eq!(
  ///   &matches1,
  ///   &[
  ///      ExpressionIndex(0), ExpressionIndex(0), ExpressionIndex(0), ExpressionIndex(0),
  ///      ExpressionIndex(0), ExpressionIndex(0),
  ///    ],
  /// );
  ///
  /// // The second db returns corresponding ExpressionIndex instances:
  /// let mut matches2: Vec<ExpressionIndex> = Vec::new();
  /// scratch.scan_sync(&set2, msg, |m| {
  ///   matches2.push(m.id);
  ///   MatchResult::Continue
  /// })?;
  /// assert_eq!(
  ///   &matches2,
  ///   &[
  ///      ExpressionIndex(300), ExpressionIndex(300), ExpressionIndex(300),
  ///      ExpressionIndex(12), ExpressionIndex(12), ExpressionIndex(12),
  ///    ],
  /// );
  /// # Ok(())
  /// # }
  /// ```
  pub fn with_ids(mut self, ids: impl IntoIterator<Item=ExprId>) -> Self {
    let ids: Vec<_> = ids.into_iter().collect();
    assert_eq!(self.len(), ids.len());
    self.ids = Some(ids.to_vec());
    self
  }

  /// Call [`Database::compile_multi_literal()`] with the result of
  /// [`Platform::get()`].
  pub fn compile(self, mode: Mode) -> Result<Database, HyperscanCompileError> {
    Database::compile_multi_literal(&self, mode, Platform::get())
  }

  /// The number of literals in this set.
  pub fn len(&self) -> usize { self.ptrs.len() }

  /// Whether this set contains any literals.
  pub fn is_empty(&self) -> bool { self.len() == 0 }

  pub(crate) fn num_elements(&self) -> c_uint { self.len() as c_uint }

  pub(crate) fn literals_ptr(&self) -> *const *const c_char { self.ptrs.as_ptr() }

  pub(crate) fn lengths_ptr(&self) -> *const usize { self.lens.as_ptr() }

  pub(crate) fn flags_ptr(&self) -> *const c_uint {
    self
      .flags
      .as_ref()
      .map(|f| unsafe { mem::transmute(f.as_ptr()) })
      .unwrap_or(ptr::null())
  }

  pub(crate) fn ids_ptr(&self) -> *const c_uint {
    self
      .ids
      .as_ref()
      .map(|i| unsafe { mem::transmute(i.as_ptr()) })
      .unwrap_or(ptr::null())
  }
}

/// Pattern strings for the chimera library.
///
/// As per [Pattern Support], chimera has full support for PCRE.
///
/// [Pattern Support]: https://intel.github.io/hyperscan/dev-reference/chimera.html#pattern-support
///
/// As chimera focuses mainly on supporting PCRE compatibility and group
/// matching support, this interface is less full-featured than the standard
/// hyperscan library [`super::expression`]. However, the same idioms apply:
/// creating expression instances performs no pattern compilation itself, and
/// references to these structs can be reused without re-allocating the
/// underlying pattern string data:
///
///```
/// # #[allow(unused_variables)]
/// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
/// use hyperscan::{expression::chimera::*, flags::chimera::*};
///
/// let a: ChimeraExpression = "a+".parse()?;
/// let b: ChimeraExpression = "b+".parse()?;
/// let c: ChimeraExpression = "c+".parse()?;
///
/// let ab_db = ChimeraExpressionSet::from_exprs([&a, &b]).compile(ChimeraMode::NOGROUPS)?;
/// let bc_db = ChimeraExpressionSet::from_exprs([&b, &c]).compile(ChimeraMode::NOGROUPS)?;
/// let ca_db = ChimeraExpressionSet::from_exprs([&c, &a]).compile(ChimeraMode::NOGROUPS)?;
/// # Ok(())
/// # }
/// ```
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::ExprId;
  use crate::{
    database::{chimera::ChimeraDb, Platform},
    error::chimera::ChimeraCompileError,
    flags::chimera::{ChimeraFlags, ChimeraMode},
  };

  use std::{
    ffi::{CStr, CString},
    fmt,
    marker::PhantomData,
    mem,
    os::raw::{c_char, c_uint, c_ulong},
    ptr, str,
  };

  /// Chimera (PCRE) pattern string.
  ///
  /// Note that as the underlying chimera library interprets pattern strings
  /// as essentially null-terminated [`CStr`] pointers, null
  /// bytes are *not* supported within `ChimeraExpression` strings (or by the
  /// chimera library in general).
  ///
  /// Instances can be created equivalently with [`Self::new()`] or
  /// [`str::parse()`] via the [`str::FromStr`] impl:
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
  /// use hyperscan::expression::chimera::ChimeraExpression;
  ///
  /// let e1: ChimeraExpression = "asd(f+)".parse()?;
  /// let e2 = ChimeraExpression::new("asd(f+)")?;
  /// assert_eq!(e1, e2);
  /// # Ok(())
  /// # }
  /// ```
  #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

  impl fmt::Display for ChimeraExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      let b = self.as_bytes();
      match str::from_utf8(b) {
        Ok(s) => write!(f, "{}", s),
        Err(_) => write!(f, "(non-utf8: {:?})", b),
      }
    }
  }

  impl ChimeraExpression {
    /// Reference the underlying bytes, *without* the trailing null terminator.
    ///
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// let e = hyperscan::expression::chimera::ChimeraExpression::new("asd(f+)")?;
    /// assert_eq!(e.as_bytes(), b"asd(f+)");
    /// # Ok(())
    /// # }
    /// ```
    pub fn as_bytes(&self) -> &[u8] { self.0.as_bytes() }

    pub(crate) fn as_ptr(&self) -> *const c_char { self.0.as_c_str().as_ptr() }

    /// Produce a `NULL`-terminated C-style wrapper for the given pattern
    /// string.
    ///
    /// This will fail if the string contains any internal `NULL` bytes, as
    /// those are not supported by the chimera library:
    ///```
    /// use hyperscan::{expression::chimera::*, error::chimera::*};
    ///
    /// let pat = "as\0df";
    /// let e = match ChimeraExpression::new(pat) {
    ///    Err(ChimeraCompileError::NullByte(e)) => e,
    ///    _ => unreachable!(),
    /// };
    /// assert_eq!(e.nul_position(), 2);
    /// ```
    pub fn new(x: impl Into<Vec<u8>>) -> Result<Self, ChimeraCompileError> {
      Ok(Self(CString::new(x)?))
    }

    /// Call [`ChimeraDb::compile()`] with the result of [`Platform::get()`].
    pub fn compile(
      &self,
      flags: ChimeraFlags,
      mode: ChimeraMode,
    ) -> Result<ChimeraDb, ChimeraCompileError> {
      ChimeraDb::compile(self, flags, mode, Platform::get())
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

  #[derive(Clone)]
  pub struct ChimeraExpressionSet<'a> {
    ptrs: Vec<*const c_char>,
    flags: Option<Vec<ChimeraFlags>>,
    ids: Option<Vec<ExprId>>,
    limits: Option<ChimeraMatchLimits>,
    _ph: PhantomData<&'a u8>,
  }

  impl<'a> fmt::Debug for ChimeraExpressionSet<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      let exprs: Vec<&'a CStr> = self
        .ptrs
        .iter()
        .map(|p| unsafe { CStr::from_ptr(*p) })
        .collect();
      write!(
        f,
        "ChimeraExpressionSet(exprs={:?}, flags={:?}, ids={:?}, limits={:?})",
        exprs, &self.flags, &self.ids, &self.limits
      )
    }
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
      assert_eq!(self.len(), flags.len());
      self.flags = Some(flags);
      self
    }

    pub fn with_ids(mut self, ids: impl IntoIterator<Item=ExprId>) -> Self {
      let ids: Vec<_> = ids.into_iter().collect();
      assert_eq!(self.len(), ids.len());
      self.ids = Some(ids);
      self
    }

    pub fn with_limits(mut self, limits: ChimeraMatchLimits) -> Self {
      self.limits = Some(limits);
      self
    }

    /// Call [`ChimeraDb::compile_multi()`] with the result of
    /// [`Platform::get()`].
    pub fn compile(self, mode: ChimeraMode) -> Result<ChimeraDb, ChimeraCompileError> {
      ChimeraDb::compile_multi(&self, mode, Platform::get())
    }

    pub fn len(&self) -> usize { self.ptrs.len() }

    pub fn is_empty(&self) -> bool { self.len() == 0 }

    pub(crate) fn limits(&self) -> Option<ChimeraMatchLimits> { self.limits }

    pub(crate) fn num_elements(&self) -> c_uint { self.len() as c_uint }

    pub(crate) fn expressions_ptr(&self) -> *const *const c_char { self.ptrs.as_ptr() }

    pub(crate) fn flags_ptr(&self) -> *const c_uint {
      self
        .flags
        .as_ref()
        .map(|f| unsafe { mem::transmute(f.as_ptr()) })
        .unwrap_or(ptr::null())
    }

    pub(crate) fn ids_ptr(&self) -> *const c_uint {
      self
        .ids
        .as_ref()
        .map(|i| unsafe { mem::transmute(i.as_ptr()) })
        .unwrap_or(ptr::null())
    }
  }
}

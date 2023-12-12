/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::hs;

use std::{
  ops,
  os::raw::{c_uint, c_ulonglong},
};

trait BitSet:
  Copy+ops::BitOr<Output=Self>+ops::BitOrAssign+ops::BitAnd<Output=Self>+ops::BitAndAssign
{
  fn nonzero(&self) -> bool;
  fn contains(&self, other: &Self) -> bool { (*self & *other).nonzero() }
}

/* NB: This MUST have the same representation as a c_uint in order to
 * mem::transmute a vector of these into a vector of c_uint! */
/// Flags which modify the behaviour of each expression. Multiple flags may be
/// used by ORing them together.
///
/// Note that flags may always be overridden by switches in the pattern string
/// such as `(?i)` for case-insensitive matching.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Flags(c_uint);

/// Basic expression matching flags.
impl Flags {
  /// Matching will be performed case-insensitively.
  ///
  /// This flag sets the expression to be matched case-insensitively by default.
  /// The expression may still use PCRE tokens (notably `(?i)` and
  /// `(?-i)`) to switch case-insensitive matching on and off.
  pub const CASELESS: Self = Self(hs::HS_FLAG_CASELESS as c_uint);
  /// Matching a `.` will not exclude newlines.
  ///
  /// This flag sets any instances of the `.` token to match newline characters
  /// as well as all other characters. The PCRE specification states that the
  /// `.` token does not match newline characters by default, so without this
  /// flag the `.` token will not cross line boundaries.
  pub const DOTALL: Self = Self(hs::HS_FLAG_DOTALL as c_uint);
  /// `^` and `$` anchors match any newlines in data.
  ///
  /// This flag instructs the expression to make the `^` and `$` tokens match
  /// newline characters as well as the start and end of the stream. If this
  /// flag is not specified, the `^` token will only ever match at the start
  /// of a stream, and the `$` token will only ever match at the end of a
  /// stream within the guidelines of the PCRE specification.
  pub const MULTILINE: Self = Self(hs::HS_FLAG_MULTILINE as c_uint);
  /// Allow expressions which can match against an empty string, such as `.*`.
  ///
  /// This flag instructs the compiler to allow expressions that can match
  /// against empty buffers, such as `.?`, `.*`, `(a|)`. Since Hyperscan can
  /// return every possible match for an expression, such expressions
  /// generally execute very slowly; the default behaviour is to return an
  /// error when an attempt to compile one is made. Using this flag will force
  /// the compiler to allow such an expression.
  pub const ALLOWEMPTY: Self = Self(hs::HS_FLAG_ALLOWEMPTY as c_uint);
  /// Enable UTF-8 mode for this expression.
  ///
  /// This flag instructs Hyperscan to treat the pattern as a sequence of UTF-8
  /// characters. The results of scanning invalid UTF-8 sequences with a
  /// Hyperscan library that has been compiled with one or more patterns using
  /// this flag are undefined.
  pub const UTF8: Self = Self(hs::HS_FLAG_UTF8 as c_uint);
  /// Enable Unicode property support for this expression.
  ///
  /// This flag instructs Hyperscan to use Unicode properties, rather than the
  /// default ASCII interpretations, for character mnemonics like `\w` and `\s`
  /// as well as the POSIX character classes. It is only meaningful in
  /// conjunction with [`Self::UTF8`].
  pub const UCP: Self = Self(hs::HS_FLAG_UCP as c_uint);

  pub(crate) const fn into_native(self) -> c_uint { self.0 as c_uint }
}

/// These flags have a more complex effect on expression parsing or matching.
impl Flags {
  /// Only one match will be generated by patterns with this match id per
  /// stream.
  ///
  /// This flag sets the expression's match ID to match at most once. In
  /// streaming mode, this means that the expression will return only a single
  /// match over the lifetime of the stream, rather than reporting every match
  /// as per standard Hyperscan semantics. In block mode or vectored mode,
  /// only the first match for each invocation of
  /// [`scan()`](crate::state::Scratch::scan) or
  /// [`scan_vectored()`](crate::state::Scratch::scan_vectored) will be
  /// returned.
  ///
  /// If multiple expressions in the database share the same match ID, then they
  /// either must all specify `SINGLEMATCH` or none of them specify
  /// `SINGLEMATCH`. If a group of expressions sharing a match ID
  /// specify the flag, then at most one match with the match ID will be
  /// generated per stream.
  ///
  /// Note: The use of this flag in combination with [`Self::SOM_LEFTMOST`]
  /// is not currently supported.
  pub const SINGLEMATCH: Self = Self(hs::HS_FLAG_SINGLEMATCH as c_uint);
  /// Parse the expression in logical combination syntax.
  ///
  /// This flag instructs Hyperscan to parse this expression as logical
  /// combination syntax.
  /// Logical constraints consist of operands, operators and parentheses.
  /// The operands are expression indices, and operators can be:
  /// - `!` (NOT),
  /// - `&` (AND), or
  /// - `|` (OR).
  ///
  /// For example:
  ///```c
  /// (101&102&103)|(104&!105)
  /// ((301|302)&303)&(304|305)
  /// ```
  pub const COMBINATION: Self = Self(hs::HS_FLAG_COMBINATION as c_uint);
  /// Compile pattern in prefiltering mode.
  ///
  /// This flag instructs Hyperscan to compile an "approximate" version of this
  /// pattern for use in a prefiltering application, even if Hyperscan does not
  /// support the pattern in normal operation.
  ///
  /// The set of matches returned when this flag is used is guaranteed to be a
  /// superset of the matches specified by the non-prefiltering expression.
  ///
  /// If the pattern contains pattern constructs not supported by Hyperscan
  /// (such as zero-width assertions, back-references or conditional
  /// references) these constructs will be replaced internally with broader
  /// constructs that may match more often.
  ///
  /// Furthermore, in prefiltering mode Hyperscan may simplify a pattern that
  /// would otherwise return a "Pattern too large" error at compile time, or for
  /// performance reasons (subject to the matching guarantee above).
  ///
  /// It is generally expected that the application will subsequently confirm
  /// prefilter matches with another regular expression matcher that can provide
  /// exact matches for the pattern.
  ///
  /// Note: The use of this flag in combination with [`Self::SOM_LEFTMOST`]
  /// is not currently supported.
  pub const PREFILTER: Self = Self(hs::HS_FLAG_PREFILTER as c_uint);
  /// Ignore match reporting for this expression. Used for the sub-expressions
  /// in logical combinations.
  pub const QUIET: Self = Self(hs::HS_FLAG_QUIET as c_uint);
  /// Report the leftmost start of match offset when a match is found.
  ///
  /// This flag instructs Hyperscan to report the leftmost possible start of
  /// match offset when a match is reported for this expression. (By default,
  /// no start of match is returned.)
  ///
  /// For all the 3 modes [`Mode::SOM_HORIZON_LARGE`],
  /// [`Mode::SOM_HORIZON_MEDIUM`], and [`Mode::SOM_HORIZON_SMALL`], enabling
  /// this behaviour may reduce performance. And particularly, it may increase
  /// stream state requirements in streaming mode.
  pub const SOM_LEFTMOST: Self = Self(hs::HS_FLAG_SOM_LEFTMOST as c_uint);
}

impl BitSet for Flags {
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for Flags {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for Flags {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for Flags {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}

impl ops::BitAndAssign for Flags {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}


/// Compiler mode flags that affect the database as a whole.
///
/// No [`Default`] impl is provided to enforce that at least one of
/// [`STREAM`](Self::STREAM), [`BLOCK`](Self::BLOCK), or
/// [`VECTORED`](Self::VECTORED) is supplied, to select between the generation
/// of a streaming, block or vectored database. In addition, other flags may be
/// supplied to enable or configure specific features such as stream state size.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Mode(u32);

static_assertions::const_assert_eq!(hs::HS_MODE_BLOCK, hs::HS_MODE_NOSTREAM);

/// Basic database types.
///
/// For now, each database can only be one type (this is checked by hyperscan
/// upon database creation).
impl Mode {
  /// Block scan (non-streaming) database.
  pub const BLOCK: Self = Self(hs::HS_MODE_BLOCK as u32);
  /// Alias for [`BLOCK`](Self::BLOCK).
  pub const NOSTREAM: Self = Self(hs::HS_MODE_NOSTREAM as u32);
  /// Streaming database.
  pub const STREAM: Self = Self(hs::HS_MODE_STREAM as u32);
  /// Vectored scanning database.
  pub const VECTORED: Self = Self(hs::HS_MODE_VECTORED as u32);

  pub(crate) const fn into_native(self) -> c_uint { self.0 as c_uint }
}

/// Stream state precision modes.
///
/// These flags are currently only processed when [`Self::STREAM`] is requested.
impl Mode {
  /// Use full precision to track start of match offsets in stream state.
  ///
  /// This mode will use the most stream state per pattern, but will always
  /// return an accurate start of match offset regardless of how far back in
  /// the past it was found.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_LARGE: Self = Self(hs::HS_MODE_SOM_HORIZON_LARGE);
  /// Use medium precision to track start of match offsets in
  /// stream state.
  ///
  /// This mode will use less stream state than
  /// [`Self::SOM_HORIZON_LARGE`] and will limit start of
  /// match accuracy to offsets within 2^32 bytes of the end of match offset
  /// reported.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_MEDIUM: Self = Self(hs::HS_MODE_SOM_HORIZON_MEDIUM);
  /// Use limited precision to track start of match offsets in
  /// stream state.
  ///
  /// This mode will use less stream state than
  /// [`Self::SOM_HORIZON_LARGE`] and will limit start of
  /// match accuracy to offsets within 2^16 bytes of the end of match offset
  /// reported.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_SMALL: Self = Self(hs::HS_MODE_SOM_HORIZON_SMALL);
}

impl BitSet for Mode {
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for Mode {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for Mode {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for Mode {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}

impl ops::BitAndAssign for Mode {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}

/// CPU feature support flags
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CpuFeatures(u8);

impl CpuFeatures {
  /// Intel(R) Advanced Vector Extensions 2 (Intel(R) AVX2)
  ///
  /// Setting this flag indicates that the target platform supports AVX2
  /// instructions.
  pub const AVX2: Self = Self(hs::HS_CPU_FEATURES_AVX2);
  /// Intel(R) Advanced Vector Extensions 512 (Intel(R) AVX512)
  ///
  /// Setting this flag indicates that the target platform supports AVX512
  /// instructions, specifically AVX-512BW. Using AVX512 implies the use of
  /// AVX2.
  pub const AVX512: Self = Self(hs::HS_CPU_FEATURES_AVX512);
  /// Intel(R) Advanced Vector Extensions 512 Vector Byte Manipulation
  /// Instructions (Intel(R) AVX512VBMI)
  ///
  /// Setting this flag indicates that the target platform supports AVX512VBMI
  /// instructions. Using AVX512VBMI implies the use of AVX512.
  pub const AVX512VBMI: Self = Self(hs::HS_CPU_FEATURES_AVX512VBMI);

  pub(crate) const fn into_native(self) -> c_ulonglong { self.0 as c_ulonglong }

  pub(crate) const fn from_native(x: c_ulonglong) -> Self { Self(x as u8) }
}

impl BitSet for CpuFeatures {
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for CpuFeatures {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for CpuFeatures {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for CpuFeatures {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}

impl ops::BitAndAssign for CpuFeatures {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}

/// Tuning flags
#[derive(
  Debug,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::FromPrimitive,
  num_enum::IntoPrimitive,
)]
#[repr(u8)]
pub enum TuneFamily {
  /// Generic
  ///
  /// This indicates that the compiled database should not be tuned for any
  /// particular target platform.
  #[num_enum(default)]
  Generic = hs::HS_TUNE_FAMILY_GENERIC,
  /// Intel(R) microarchitecture code name Sandy Bridge
  SandyBridge = hs::HS_TUNE_FAMILY_SNB,
  /// Intel(R) microarchitecture code name Ivy Bridge
  IvyBridge = hs::HS_TUNE_FAMILY_IVB,
  /// Intel(R) microarchitecture code name Haswell
  Haswell = hs::HS_TUNE_FAMILY_HSW,
  /// Intel(R) microarchitecture code name Silvermont
  Silvermont = hs::HS_TUNE_FAMILY_SLM,
  /// Intel(R) microarchitecture code name Broadwell
  Broadwell = hs::HS_TUNE_FAMILY_BDW,
  /// Intel(R) microarchitecture code name Skylake
  Skylake = hs::HS_TUNE_FAMILY_SKL,
  /// Intel(R) microarchitecture code name Skylake Server
  SkylakeServer = hs::HS_TUNE_FAMILY_SKX,
  /// Intel(R) microarchitecture code name Goldmont
  Goldmont = hs::HS_TUNE_FAMILY_GLM,
  /// Intel(R) microarchitecture code name Icelake
  Icelake = hs::HS_TUNE_FAMILY_ICL,
  /// Intel(R) microarchitecture code name Icelake Server
  IcelakeServer = hs::HS_TUNE_FAMILY_ICX,
}

impl TuneFamily {
  /* FIXME: make num_enum support const fn! */
  pub(crate) fn into_native(self) -> c_uint {
    let x: u8 = self.into();
    x as c_uint
  }

  pub(crate) fn from_native(x: c_uint) -> Self { (x as u8).into() }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub(crate) struct ExtFlags(u8);

impl ExtFlags {
  pub const EDIT_DISTANCE: Self = Self(hs::HS_EXT_FLAG_EDIT_DISTANCE);
  pub const HAMMING_DISTANCE: Self = Self(hs::HS_EXT_FLAG_HAMMING_DISTANCE);
  pub const MAX_OFFSET: Self = Self(hs::HS_EXT_FLAG_MAX_OFFSET);
  pub const MIN_LENGTH: Self = Self(hs::HS_EXT_FLAG_MIN_LENGTH);
  pub const MIN_OFFSET: Self = Self(hs::HS_EXT_FLAG_MIN_OFFSET);

  pub fn has_edit_distance(&self) -> bool { self.contains(&Self::EDIT_DISTANCE) }

  pub fn has_hamming_distance(&self) -> bool { self.contains(&Self::HAMMING_DISTANCE) }

  pub fn has_max_offset(&self) -> bool { self.contains(&Self::MAX_OFFSET) }

  pub fn has_min_length(&self) -> bool { self.contains(&Self::MIN_LENGTH) }

  pub fn has_min_offset(&self) -> bool { self.contains(&Self::MIN_OFFSET) }

  pub(crate) const fn into_native(self) -> c_ulonglong { self.0 as c_ulonglong }

  pub(crate) const fn from_native(x: c_ulonglong) -> Self { Self(x as u8) }
}

impl BitSet for ExtFlags {
  fn nonzero(&self) -> bool { self.0 != 0 }
}

impl ops::BitOr for ExtFlags {
  type Output = Self;

  fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
}

impl ops::BitOrAssign for ExtFlags {
  fn bitor_assign(&mut self, rhs: Self) {
    use ops::BitOr;
    *self = self.bitor(rhs);
  }
}

impl ops::BitAnd for ExtFlags {
  type Output = Self;

  fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
}


impl ops::BitAndAssign for ExtFlags {
  fn bitand_assign(&mut self, rhs: Self) {
    use ops::BitAnd;
    *self = self.bitand(rhs);
  }
}

#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::BitSet;
  use crate::hs;

  use std::{ops, os::raw::c_uint};

  /* NB: This MUST have the same representation as a c_uint in order to
   * mem::transmute a vector of these into a vector of c_uint! */
  /// Pattern flags
  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct ChimeraFlags(c_uint);

  impl ChimeraFlags {
    /// Set case-insensitive matching.
    ///
    /// This flag sets the expression to be matched case-insensitively by
    /// default. The expression may still use PCRE tokens (notably `(?i)`
    /// and `(?-i)`) to switch case-insensitive matching on and off.
    pub const CASELESS: Self = Self(hs::CH_FLAG_CASELESS as c_uint);
    /// Matching a `.` will not exclude newlines.
    ///
    /// This flag sets any instances of the `.` token to match newline
    /// characters as well as all other characters. The PCRE specification
    /// states that the `.` token does not match newline characters by
    /// default, so without this flag the `.` token will not cross line
    /// boundaries.
    pub const DOTALL: Self = Self(hs::CH_FLAG_DOTALL as c_uint);
    /// Set multi-line anchoring.
    ///
    /// This flag instructs the expression to make the `^` and `$` tokens match
    /// newline characters as well as the start and end of the stream. If this
    /// flag is not specified, the `^` token will only ever match at the start
    /// of a stream, and the `$` token will only ever match at the end of a
    /// stream within the guidelines of the PCRE specification.
    pub const MULTILINE: Self = Self(hs::CH_FLAG_MULTILINE as c_uint);
    /// Set single-match only mode.
    ///
    /// This flag sets the expression's match ID to match at most once, only the
    /// first match for each invocation of @ref ch_scan() will be returned.
    pub const SINGLEMATCH: Self = Self(hs::CH_FLAG_SINGLEMATCH as c_uint);
    /// Enable UTF-8 mode for this expression.
    ///
    /// This flag instructs Chimera to treat the pattern as a sequence of UTF-8
    /// characters. The results of scanning invalid UTF-8 sequences with a
    /// Chimera library that has been compiled with one or more patterns
    /// using this flag are undefined.
    pub const UTF8: Self = Self(hs::CH_FLAG_UTF8 as c_uint);
    /// Enable Unicode property support for this expression.
    ///
    /// This flag instructs Chimera to use Unicode properties, rather than the
    /// default ASCII interpretations, for character mnemonics like `\w` and
    /// `\s` as well as the POSIX character classes. It is only meaningful
    /// in conjunction with @ref CH_FLAG_UTF8.
    pub const UCP: Self = Self(hs::CH_FLAG_UCP as c_uint);

    pub(crate) const fn into_native(self) -> c_uint { self.0 as c_uint }
  }

  impl BitSet for ChimeraFlags {
    fn nonzero(&self) -> bool { self.0 != 0 }
  }

  impl ops::BitOr for ChimeraFlags {
    type Output = Self;

    fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
  }

  impl ops::BitOrAssign for ChimeraFlags {
    fn bitor_assign(&mut self, rhs: Self) {
      use ops::BitOr;
      *self = self.bitor(rhs);
    }
  }

  impl ops::BitAnd for ChimeraFlags {
    type Output = Self;

    fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
  }

  impl ops::BitAndAssign for ChimeraFlags {
    fn bitand_assign(&mut self, rhs: Self) {
      use ops::BitAnd;
      *self = self.bitand(rhs);
    }
  }

  /// Compile mode flags
  ///
  /// The mode flags are used as values for the mode parameter of the various
  /// compile calls
  /// ([`compile()`](crate::database::chimera::ChimeraDb::compile),
  /// [`compile_multi()`](crate::database::chimera::ChimeraDb::compile_multi)).
  ///
  /// By default, the matcher will only supply the start and end offsets of the
  /// match when the match callback is called. Using mode flag
  /// [`Self::GROUPS`] will also fill the `captured' array with the start and
  /// end offsets of all the capturing groups specified by the pattern that
  /// has matched.
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct ChimeraMode(u32);

  impl ChimeraMode {
    /// Enable capturing groups.
    pub const GROUPS: Self = Self(hs::CH_MODE_GROUPS);
    /// Disable capturing groups.
    pub const NOGROUPS: Self = Self(hs::CH_MODE_NOGROUPS as u32);

    pub(crate) const fn into_native(self) -> c_uint { self.0 as c_uint }
  }

  impl BitSet for ChimeraMode {
    fn nonzero(&self) -> bool { self.0 != 0 }
  }

  impl ops::BitOr for ChimeraMode {
    type Output = Self;

    fn bitor(self, other: Self) -> Self { Self(self.0.bitor(other.0)) }
  }

  impl ops::BitOrAssign for ChimeraMode {
    fn bitor_assign(&mut self, rhs: Self) {
      use ops::BitOr;
      *self = self.bitor(rhs);
    }
  }

  impl ops::BitAnd for ChimeraMode {
    type Output = Self;

    fn bitand(self, other: Self) -> Self { Self(self.0.bitand(other.0)) }
  }

  impl ops::BitAndAssign for ChimeraMode {
    fn bitand_assign(&mut self, rhs: Self) {
      use ops::BitAnd;
      *self = self.bitand(rhs);
    }
  }
}

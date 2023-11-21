/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{error::HyperscanFlagsError, hs};

use std::{
  ops,
  os::raw::{c_uint, c_ulonglong},
};

pub(crate) trait BitSet:
  Copy+ops::BitOr<Output=Self>+ops::BitOrAssign+ops::BitAnd<Output=Self>+ops::BitAndAssign
{
  fn nonzero(&self) -> bool;
  #[inline]
  fn contains(&self, other: &Self) -> bool { (*self & *other).nonzero() }
}

/// Flags which modify the behaviour of each expression. Multiple flags may be
/// used by ORing them together.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Flags(u32);

impl Flags {
  /// Allow expressions which can match against an empty string, such as `.*`.
  pub const ALLOWEMPTY: Self = Self(hs::HS_FLAG_ALLOWEMPTY as u32);
  /// Matching will be performed case-insensitively.
  pub const CASELESS: Self = Self(hs::HS_FLAG_CASELESS as u32);
  /// Parse the expression in logical combination syntax.
  pub const COMBINATION: Self = Self(hs::HS_FLAG_COMBINATION as u32);
  /// Matching a `.` will not exclude newlines.
  pub const DOTALL: Self = Self(hs::HS_FLAG_DOTALL as u32);
  /// `^` and `$` anchors match any newlines in data.
  pub const MULTILINE: Self = Self(hs::HS_FLAG_MULTILINE as u32);
  /// Compile pattern in prefiltering mode.
  pub const PREFILTER: Self = Self(hs::HS_FLAG_PREFILTER as u32);
  /// Ignore match reporting for this expression. Used for the sub-expressions
  /// in logical combinations.
  pub const QUIET: Self = Self(hs::HS_FLAG_QUIET as u32);
  /// Only one match will be generated by patterns with this match id per
  /// stream.
  pub const SINGLEMATCH: Self = Self(hs::HS_FLAG_SINGLEMATCH as u32);
  /// Report the leftmost start of match offset when a match is found.
  pub const SOM_LEFTMOST: Self = Self(hs::HS_FLAG_SOM_LEFTMOST as u32);
  /// Use Unicode properties for character classes.
  pub const UCP: Self = Self(hs::HS_FLAG_UCP as u32);
  /// Treat this pattern as a sequence of UTF-8 characters.
  pub const UTF8: Self = Self(hs::HS_FLAG_UTF8 as u32);

  #[inline(always)]
  pub(crate) const fn into_native(self) -> c_uint { self.0 as c_uint }
}

impl BitSet for Flags {
  #[inline]
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
/// of a streaming, block or vectored database. In addition, other flags
/// (beginning with HS_MODE_) may be supplied to enable specific features. See
/// @ref HS_MODE_FLAG for more details.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Mode(u32);

static_assertions::const_assert_eq!(hs::HS_MODE_BLOCK, hs::HS_MODE_NOSTREAM);

impl Mode {
  /// Block scan (non-streaming) database.
  pub const BLOCK: Self = Self(hs::HS_MODE_BLOCK as u32);
  /// Alias for [`BLOCK`](Self::BLOCK).
  pub const NOSTREAM: Self = Self(hs::HS_MODE_NOSTREAM as u32);
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
  /// [`SOM_HORIZON_LARGE`](Self::SOM_HORIZON_LARGE) and will limit start of
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
  /// [`SOM_HORIZON_LARGE`](Self::SOM_HORIZON_LARGE) and will limit start of
  /// match accuracy to offsets within 2^16 bytes of the end of match offset
  /// reported.
  ///
  /// One of the `SOM_HORIZON_*` modes must be selected to use the
  /// [`Flags::SOM_LEFTMOST`] expression flag.
  pub const SOM_HORIZON_SMALL: Self = Self(hs::HS_MODE_SOM_HORIZON_SMALL);
  /// Streaming database.
  pub const STREAM: Self = Self(hs::HS_MODE_STREAM as u32);
  /// Vectored scanning database.
  pub const VECTORED: Self = Self(hs::HS_MODE_VECTORED as u32);

  #[inline]
  fn check_db_type(&self) -> bool {
    self.contains(&Self::NOSTREAM) || self.contains(&Self::STREAM) || self.contains(&Self::VECTORED)
  }

  #[inline]
  pub fn validate_db_type(&self) -> Result<(), HyperscanFlagsError> {
    if self.check_db_type() {
      Ok(())
    } else {
      Err(HyperscanFlagsError::InvalidDbMode)
    }
  }

  #[inline]
  fn any_som_horizon_mode_was_selected(&self) -> bool {
    self.contains(&Self::SOM_HORIZON_LARGE)
      || self.contains(&Self::SOM_HORIZON_MEDIUM)
      || self.contains(&Self::SOM_HORIZON_SMALL)
  }

  #[inline]
  pub fn validate_against_flags(&self, flags: &Flags) -> Result<(), HyperscanFlagsError> {
    if flags.contains(&Flags::SOM_LEFTMOST) && !self.any_som_horizon_mode_was_selected() {
      Err(HyperscanFlagsError::SomHorizonModeRequired)
    } else {
      Ok(())
    }
  }

  #[inline(always)]
  pub(crate) const fn into_native(self) -> c_uint { self.0 as c_uint }
}

impl BitSet for Mode {
  #[inline]
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

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CpuFeatures(u8);

impl CpuFeatures {
  pub const AVX2: Self = Self(hs::HS_CPU_FEATURES_AVX2);
  pub const AVX512: Self = Self(hs::HS_CPU_FEATURES_AVX512);
  pub const AVX512VBMI: Self = Self(hs::HS_CPU_FEATURES_AVX512VBMI);

  #[inline(always)]
  pub(crate) const fn into_native(self) -> c_ulonglong { self.0 as c_ulonglong }

  #[inline(always)]
  pub(crate) const fn from_native(x: c_ulonglong) -> Self { Self(x as u8) }
}

impl BitSet for CpuFeatures {
  #[inline]
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
  #[inline(always)]
  pub(crate) fn into_native(self) -> c_uint {
    let x: u8 = self.into();
    x as c_uint
  }

  #[inline(always)]
  pub(crate) fn from_native(x: c_uint) -> Self { (x as u8).into() }
}


#[derive(Default, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ScanFlags(c_uint);

impl ScanFlags {
  #[inline(always)]
  pub const fn from_native(x: c_uint) -> Self { Self(x) }

  #[inline(always)]
  pub const fn into_native(self) -> c_uint { self.0 }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExtFlags(u8);

impl ExtFlags {
  pub const EDIT_DISTANCE: Self = Self(hs::HS_EXT_FLAG_EDIT_DISTANCE);
  pub const HAMMING_DISTANCE: Self = Self(hs::HS_EXT_FLAG_HAMMING_DISTANCE);
  pub const MAX_OFFSET: Self = Self(hs::HS_EXT_FLAG_MAX_OFFSET);
  pub const MIN_LENGTH: Self = Self(hs::HS_EXT_FLAG_MIN_LENGTH);
  pub const MIN_OFFSET: Self = Self(hs::HS_EXT_FLAG_MIN_OFFSET);

  #[inline]
  pub fn has_edit_distance(&self) -> bool { self.contains(&Self::EDIT_DISTANCE) }

  #[inline]
  pub fn has_hamming_distance(&self) -> bool { self.contains(&Self::HAMMING_DISTANCE) }

  #[inline]
  pub fn has_max_offset(&self) -> bool { self.contains(&Self::MAX_OFFSET) }

  #[inline]
  pub fn has_min_length(&self) -> bool { self.contains(&Self::MIN_LENGTH) }

  #[inline]
  pub fn has_min_offset(&self) -> bool { self.contains(&Self::MIN_OFFSET) }

  #[inline(always)]
  pub(crate) const fn into_native(self) -> c_ulonglong { self.0 as c_ulonglong }

  #[inline(always)]
  pub(crate) const fn from_native(x: c_ulonglong) -> Self { Self(x as u8) }
}

impl BitSet for ExtFlags {
  #[inline]
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

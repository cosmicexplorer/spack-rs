/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Configuration accepted by the pattern compiler.

use crate::re2;
#[cfg(doc)]
use crate::{string::StringView, RE2};

use displaydoc::Display;

use std::os::raw::c_uint;

/// Predefined common options.
///
/// If you need more complicated things, modify an [`Options`] object directly.
/// This can be converted into [`Options`] by calling `.into()`:
///```
/// use re2::options::*;
///
/// let p = Options::default();
/// assert_eq!(p.posix_syntax, false);
/// let o: Options = CannedOptions::POSIX.into();
/// assert_eq!(o.posix_syntax, true);
/// ```
#[derive(
  Default,
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
  num_enum::TryFromPrimitive,
)]
#[repr(u32)]
pub enum CannedOptions {
  #[default]
  /// Generate [`Options::default()`].
  DefaultOptions = re2::RE2_CannedOptions_DefaultOptions,
  /// Treat input as Latin-1 (default UTF-8).
  Latin1 = re2::RE2_CannedOptions_Latin1,
  /// POSIX syntax, leftmost-longest match.
  POSIX = re2::RE2_CannedOptions_POSIX,
  /// Do not log about regexp parse errors.
  Quiet = re2::RE2_CannedOptions_Quiet,
}

impl CannedOptions {
  pub(crate) fn into_native(self) -> re2::RE2_CannedOptions { self.into() }
}

/// Encoding of text inputs.
///
/// When [`Self::Utf8`] is selected (the default), `re2` will happily accept
/// [`str`] patterns and inputs:
///```
/// # fn main() -> Result<(), re2::RE2Error> {
/// use re2::{*, options::*};
///
/// let r: RE2 = "asdf".parse()?;
/// assert_eq!(Encoding::Utf8, r.options().encoding);
/// assert!(r.full_match("asdf"));
/// # Ok(())
/// # }
/// ```
///
/// However, `re2` will also accept Latin-1 encoded text. Each string method has
/// a `*_view`-suffixed version which accepts a [`StringView`], which can
/// represent a slice of arbitrary bytes:
///```
/// # fn main() -> Result<(), re2::RE2Error> {
/// use re2::{*, options::*, string::*};
///
/// let o: Options = CannedOptions::Latin1.into();
/// let r = RE2::compile(StringView::from_slice(b"asdf"), o)?;
/// assert_eq!(Encoding::Latin1, r.options().encoding);
/// assert!(r.full_match_view(StringView::from_slice(b"asdf")));
/// # Ok(())
/// # }
/// ```
#[derive(
  Default,
  Display,
  Debug,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::IntoPrimitive,
  num_enum::TryFromPrimitive,
)]
#[repr(u32)]
pub enum Encoding {
  /// Assume UTF-8 encoded text.
  #[default]
  Utf8 = re2::RE2_Options_Encoding_EncodingUTF8,
  /// Assume Latin-1 encoded text.
  Latin1 = re2::RE2_Options_Encoding_EncodingLatin1,
}

impl Encoding {
  pub(crate) fn into_native(self) -> re2::RE2_Options_Encoding { self.into() }
}

/// Options to configure support for POSIX egrep syntax features.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PosixOptions {
  /// Allow perl's `\d`, `\s`, `\w`, `\D`, `\S`, and `\W`.
  pub perl_classes: bool,
  /// Allow perl's `\b` and `\B` (word boundary and not).
  pub word_boundary: bool,
  /// `^` and `$` only match beginning and end of text.
  pub one_line: bool,
}

/// Options to configure compilation or search behavior.
///
/// The regexp pattern may supplement these options with PCRE-like options in
/// the pattern string itself, such as `(?i)` for case-insensitive matching.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Options {
  /// Encoding of text to assume.
  pub encoding: Encoding,
  /// Restrict regexps to POSIX egrep syntax.
  pub posix_syntax: bool,
  /// Search for longest match, not first match.
  pub longest_match: bool,
  /// Log syntax and execution errors to `ERROR` (as defined in C++).
  pub log_errors: bool,
  /// Interpret string as literal, not regexp.
  pub literal: bool,
  /// Never match `\n`, even if it is in the regexp.
  pub never_nl: bool,
  /// Dot matches everything including new line.
  pub dot_nl: bool,
  /// Parse all parens as non-capturing.
  pub never_capture: bool,
  /// Match is case-sensitive.
  ///
  /// The regexp pattern can override this with `(?i)` unless
  /// [`Self::posix_syntax`] is activated.
  pub case_sensitive: bool,
  /// Options available when [`Self::posix_syntax`] is `true`.
  ///
  /// When [`Self::posix_syntax`] is `false`, these features are always
  /// enabled and cannot be turned off; to perform multi-line matching in that
  /// case, begin the regexp with `(?m)`.
  pub posix_options: PosixOptions,
  /// Approximate maximum memory footprint used by the matching engine.
  ///
  /// The `max_mem` option controls how much memory can be used
  /// to hold the compiled form of the regexp (the Prog) and
  /// its cached DFA graphs.  Code Search placed limits on the number
  /// of Prog instructions and DFA states: 10,000 for both.
  /// In RE2, those limits would translate to about 240 KB per Prog
  /// and perhaps 2.5 MB per DFA (DFA state sizes vary by regexp; RE2 does a
  /// better job of keeping them small than Code Search did).
  /// Each RE2 has two Progs (one forward, one reverse), and each Prog
  /// can have two DFAs (one first match, one longest match).
  /// That makes 4 DFAs:
  ///
  ///   forward, first-match    - used for UNANCHORED or ANCHOR_START searches
  ///                               if opt.longest_match() == false
  ///   forward, longest-match  - used for all ANCHOR_BOTH searches,
  ///                               and the other two kinds if
  ///                               opt.longest_match() == true
  ///   reverse, first-match    - never used
  ///   reverse, longest-match  - used as second phase for unanchored searches
  ///
  /// The RE2 memory budget is statically divided between the two
  /// Progs and then the DFAs: two thirds to the forward Prog
  /// and one third to the reverse Prog.  The forward Prog gives half
  /// of what it has left over to each of its DFAs.  The reverse Prog
  /// gives it all to its longest-match DFA.
  ///
  /// Once a DFA fills its budget, it flushes its cache and starts over.
  /// If this happens too often, RE2 falls back on the NFA implementation.
  pub max_mem: u32,
}

impl Options {
  /// For now, make the default budget something close to Code Search.
  pub const DEFAULT_MAX_MEM: u32 = re2::RE2_Options_kDefaultMaxMem as u32;

  pub(crate) fn into_native(self) -> re2::RE2_Options {
    let Self {
      max_mem,
      encoding,
      posix_syntax,
      longest_match,
      log_errors,
      literal,
      never_nl,
      dot_nl,
      never_capture,
      case_sensitive,
      posix_options:
        PosixOptions {
          perl_classes,
          word_boundary,
          one_line,
        },
    } = self;
    re2::RE2_Options {
      max_mem_: max_mem as i64,
      encoding_: encoding.into_native(),
      posix_syntax_: posix_syntax,
      longest_match_: longest_match,
      log_errors_: log_errors,
      literal_: literal,
      never_nl_: never_nl,
      dot_nl_: dot_nl,
      never_capture_: never_capture,
      case_sensitive_: case_sensitive,
      perl_classes_: perl_classes,
      word_boundary_: word_boundary,
      one_line_: one_line,
    }
  }
}

impl From<re2::RE2_Options> for Options {
  fn from(x: re2::RE2_Options) -> Self {
    let re2::RE2_Options {
      max_mem_,
      encoding_,
      posix_syntax_,
      longest_match_,
      log_errors_,
      literal_,
      never_nl_,
      dot_nl_,
      never_capture_,
      case_sensitive_,
      perl_classes_,
      word_boundary_,
      one_line_,
    } = x;
    assert!(max_mem_ >= 0);
    Self {
      max_mem: max_mem_ as u32,
      encoding: encoding_.try_into().unwrap(),
      posix_syntax: posix_syntax_,
      longest_match: longest_match_,
      log_errors: log_errors_,
      literal: literal_,
      never_nl: never_nl_,
      dot_nl: dot_nl_,
      never_capture: never_capture_,
      case_sensitive: case_sensitive_,
      posix_options: PosixOptions {
        perl_classes: perl_classes_,
        word_boundary: word_boundary_,
        one_line: one_line_,
      },
    }
  }
}

impl From<CannedOptions> for Options {
  fn from(x: CannedOptions) -> Self { unsafe { re2::RE2_Options::new(x.into_native()) }.into() }
}

impl Default for Options {
  fn default() -> Self {
    static_assertions::const_assert!(re2::RE2_Options_kDefaultMaxMem >= 0);
    Self {
      max_mem: Self::DEFAULT_MAX_MEM,
      encoding: Encoding::Utf8,
      posix_syntax: false,
      longest_match: false,
      log_errors: true,
      literal: false,
      never_nl: false,
      dot_nl: false,
      never_capture: false,
      case_sensitive: true,
      posix_options: Default::default(),
    }
  }
}

/// Anchoring behavior: whether the pattern must match at the start or end of
/// the input text.
#[derive(
  Debug,
  Default,
  Display,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::TryFromPrimitive,
  num_enum::IntoPrimitive,
)]
#[repr(u32)]
pub enum Anchor {
  /// unanchored
  #[default]
  Unanchored = re2::RE2_Anchor_UNANCHORED,
  /// anchored at start
  AnchorStart = re2::RE2_Anchor_ANCHOR_START,
  /// anchored at both start and end
  AnchorBoth = re2::RE2_Anchor_ANCHOR_BOTH,
}

impl Anchor {
  pub(crate) fn into_native(self) -> c_uint { self.into() }
}

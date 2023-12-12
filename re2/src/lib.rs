/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Rust interface to the re2 regular-expression library. RE2 supports
//! Perl-style regular expressions (with extensions like `\d`, `\w`, `\s`, ...).
//!
//! # Regexp Syntax
//!
//! This module uses the `re2` library and hence supports
//! its syntax for regular expressions, which is similar to Perl's with
//! some of the more complicated things thrown away.  In particular,
//! backreferences and generalized assertions are not available, nor is `\Z`.
//!
//! See [Syntax] for the syntax supported by RE2, and a comparison with PCRE and
//! PERL regexps.
//!
//! [Syntax]: https://github.com/google/re2/wiki/Syntax
//!
//! For those not familiar with Perl's regular expressions,
//! here are some examples of the most commonly used extensions:
//!
//! - `"hello (\\w+) world"`  -- `\w` matches a "word" character
//! - `"version (\\d+)"`      -- `\d` matches a digit
//! - `"hello\\s+world"`      -- `\s` matches any whitespace character
//! - `"\\b(\\w+)\\b"`        -- `\b` matches non-empty string at word boundary
//! - `"(?i)hello"`           -- `(?i)` turns on case-insensitive matching
//! - `"/\\*(.*?)\\*/"`       -- `.*?` matches `.` minimum number of times
//!   possible
//!
//! The double backslashes are needed when writing string literals.
//! However, they should NOT be used when writing raw string literals:
//!
//! - `r"(hello (\w+) world)"`  -- `\w` matches a "word" character
//! - `r"(version (\d+))"`      -- `\d` matches a digit
//! - `r"(hello\s+world)"`      -- `\s` matches any whitespace character
//! - `r"(\b(\w+)\b)"`          -- `\b` matches non-empty string at word
//!   boundary
//! - `r"((?i)hello)"`          -- `(?i)` turns on case-insensitive matching
//! - `r"(/\*(.*?)\*/)"`        -- `.*?` matches `.` minimum number of times
//!   possible
//!
//! When using UTF-8 encoding, case-insensitive matching will perform
//! simple case folding, not full case folding.

// Warn for missing docs in general, and hard require crate-level docs.
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

pub(crate) use re2_sys::{re2, re2_c};

pub mod error;
pub use error::RE2Error;
use error::{CompileError, RE2ErrorCode, RewriteError};

pub mod options;
pub use options::{Anchor, CannedOptions, Options};

pub mod string;
use string::{StringView, StringWrapper};

pub mod set;

pub mod filtered;

use std::{
  cmp, fmt, hash,
  marker::PhantomData,
  mem::{self, MaybeUninit},
  ops, ptr, str,
};

/* TODO: use MaybeUninit::uninit_array()! */
fn uninit_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
  unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() }
}

/* TODO: use MaybeUninit::array_assume_init()! */
unsafe fn array_assume_init<T: Sized, const N: usize>(x: [MaybeUninit<T>; N]) -> [T; N] {
  let x: *const [MaybeUninit<T>; N] = &x;
  let y: *const [T; N] = mem::transmute(x);
  ptr::read(y)
}

fn map_array<T, U, const N: usize, F: Fn(T) -> U>(argv: [T; N], f: F) -> [U; N] {
  let mut ret: [MaybeUninit<U>; N] = uninit_array();
  for (output, input) in ret.iter_mut().zip(argv.into_iter()) {
    output.write(f(input));
  }
  unsafe { array_assume_init(ret) }
}

/// High-level string search and replacement with a single pattern.
///
///```
/// # fn main() -> Result<(), re2::RE2Error> {
/// use re2::RE2;
///
/// let r: RE2 = "a(.+)f".parse()?;
/// let [m] = r.full_match_capturing("asdf").unwrap();
/// assert_eq!(m, "sd");
/// # Ok(())
/// # }
/// ```
#[repr(transparent)]
pub struct RE2(re2_c::RE2Wrapper);

/// Basic components of `RE2` objects.
impl RE2 {
  /// Compile an `RE2` pattern.
  ///
  /// A [`FromStr`](str::FromStr) implementation is also provided which calls
  /// this method with [`Options::default()`]:
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, options::Options};
  ///
  /// let r = RE2::compile("asdf".into(), Options::default())?;
  /// assert!(r.full_match("asdf"));
  ///
  /// let r2: RE2 = "asdf".parse()?;
  /// assert_eq!(r, r2);
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// The error contains the original pattern string as well as a description of
  /// the compile failure:
  ///```
  /// use re2::{RE2, error::*};
  ///
  /// assert_eq!(
  ///   "a(sdf".parse::<RE2>().err().unwrap(),
  ///   CompileError {
  ///     message: "missing ): a(sdf".to_string(),
  ///     arg: "a(sdf".to_string(),
  ///     code: RE2ErrorCode::MissingParen,
  ///   },
  /// );
  /// ```
  pub fn compile(pattern: StringView, options: Options) -> Result<Self, CompileError> {
    let s = Self(unsafe { re2_c::RE2Wrapper::new(pattern.into_native(), &options.into_native()) });
    s.check_error()?;
    Ok(s)
  }

  fn check_error_code(&self) -> Result<(), RE2ErrorCode> {
    RE2ErrorCode::from_native(unsafe { self.0.error_code() })
  }

  /// Extract the pattern string provided to the compiler.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "asdf".parse()?;
  /// assert_eq!(unsafe { r.pattern().as_str() }, "asdf");
  /// # Ok(())
  /// # }
  /// ```
  pub fn pattern(&self) -> StringView { unsafe { StringView::from_native(self.0.pattern()) } }

  /// Extract the options object provided to the compiler.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = RE2::compile("asdf".into(), o)?;
  /// assert_eq!(o, r.options());
  /// assert_ne!(o, Options::default());
  /// # Ok(())
  /// # }
  /// ```
  pub fn options(&self) -> Options { unsafe { *self.0.options() }.into() }

  /// Create a new instance of this `RE2` with the same semantics.
  ///
  /// This method is largely intended for documentation purposes; [`Clone`] is
  /// not implemented because of several performance reasons to re-use the
  /// same instance, e.g. with an [`Arc`](std::sync::Arc).
  ///
  /// The matching implementation may use a lazy NFA, which is partially
  /// constructed as it is matched against input strings, so it improves
  /// performance to use a reference to the same instance where possible, to
  /// avoid reconstructing the same NFA components. Upfront compilation of this
  /// NFA is also somewhat expensive in itself (even if less expensive than a
  /// DFA), and best to avoid repeating.
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = RE2::compile("asdf".into(), o)?;
  /// assert_eq!(o, r.options());
  /// assert_ne!(o, Options::default());
  ///
  /// let r2 = r.expensive_clone();
  /// assert_eq!(&r, &r2);
  /// # Ok(())
  /// # }
  /// ```
  pub fn expensive_clone(&self) -> Self { Self::compile(self.pattern(), self.options()).unwrap() }

  fn error(&self) -> StringView { unsafe { StringView::from_native(self.0.error()) } }

  fn error_arg(&self) -> StringView { unsafe { StringView::from_native(self.0.error_arg()) } }

  fn check_error(&self) -> Result<(), CompileError> {
    self.check_error_code().map_err(|code| CompileError {
      message: String::from_utf8_lossy(self.error().as_slice()).to_string(),
      arg: String::from_utf8_lossy(self.error_arg().as_slice()).to_string(),
      code,
    })
  }

  /// Escape any metacharacters in `pattern`.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::RE2;
  ///
  /// let q = RE2::quote_meta("1.5-1.8?".into());
  /// let r: RE2 = unsafe { q.as_view().as_str() }.parse()?;
  /// assert_eq!(r"1\.5\-1\.8\?", unsafe { r.pattern().as_str() });
  /// assert!(r.full_match("1.5-1.8?"));
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// Note that literal patterns can be used instead in some cases:
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, options::Options};
  ///
  /// let o = Options { literal: true, ..Default::default() };
  /// let r = RE2::compile("1.5-1.8?".into(), o)?;
  /// assert_eq!("1.5-1.8?", unsafe { r.pattern().as_str() });
  /// assert!(r.full_match("1.5-1.8?"));
  /// # Ok(())
  /// # }
  /// ```
  pub fn quote_meta(pattern: StringView) -> StringWrapper {
    let mut out = StringWrapper::from_view(pattern);
    unsafe { re2_c::RE2Wrapper::quote_meta(pattern.into_native(), out.as_mut_native()) };
    out
  }
}

impl str::FromStr for RE2 {
  type Err = CompileError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Self::compile(StringView::from_str(s), Options::default())
  }
}

/// Deletes the underlying C++ object on drop.
impl ops::Drop for RE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

/// The useful part: the matching interface.
///
/// Matching methods tend to have a few variants:
/// - Methods with a `*_view` suffix accept and return [`StringView`] instances.
///   These may have arbitrary encodings, as opposed to UTF-8-encoded
///   [`str`](prim@str) instances.
/// - Methods with a `*_capturing` suffix will return a variable array of
///   strings corresponding to matching capture groups. For these methods,
///   requesting more groups than the result of [`Self::num_captures()`] will
///   immediately return [`None`] without performing the search.
///
/// [`Self::match_routine()`] also returns a variable array of strings, but
/// presents a slightly different interface. It is the most general matching
/// entry point along with [`Self::match_no_captures()`] and is suitable for
/// building higher-level matching interfaces.
impl RE2 {
  fn empty_result<'a, const N: usize>() -> [StringView<'a>; N] {
    assert_eq!(N, 0);
    let ret: [MaybeUninit<StringView<'a>>; N] = uninit_array();
    unsafe { array_assume_init(ret) }
  }

  fn convert_string_views<'a, const N: usize>(argv: [re2_c::StringView; N]) -> [StringView<'a>; N] {
    map_array(argv, StringView::from_native)
  }

  fn convert_strings<const N: usize>(argv: [StringView; N]) -> [&str; N] {
    map_array(argv, |s| unsafe { s.as_str() })
  }

  fn convert_from_strings<const N: usize>(argv: [&str; N]) -> [StringView; N] {
    map_array(argv, StringView::from_str)
  }

  /// [`Self::full_match()`] for arbitrary string encodings.
  pub fn full_match_view(&self, text: StringView) -> bool {
    unsafe { self.0.full_match(text.into_native()) }
  }

  /// Match against `text` without capturing. Pattern must match entire string.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a.df".parse()?;
  /// assert!(r.full_match("asdf"));
  /// assert!(!r.full_match("asdfe"));
  /// assert!(!r.full_match("basdf"));
  /// # Ok(())
  /// # }
  /// ```
  pub fn full_match(&self, text: &str) -> bool { self.full_match_view(StringView::from_str(text)) }

  /// [`Self::full_match_capturing()`] for arbitrary string encodings.
  pub fn full_match_capturing_view<'a, const N: usize>(
    &self,
    text_view: StringView<'a>,
  ) -> Option<[StringView<'a>; N]> {
    if N == 0 {
      return if self.full_match_view(text_view) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut argv: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.full_match_n(
        text_view.into_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(argv.as_mut_ptr()),
        argv.len(),
      )
    } {
      return None;
    }

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  /// Match against `text` and return a subset of declared capture groups.
  /// Pattern must match entire string.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a(.)d(f)".parse()?;
  /// assert_eq!(2, r.num_captures());
  ///
  /// let msg = "asdf";
  /// // The 0 case still works, but just calls .full_match():
  /// assert!(r.full_match_capturing::<0>(msg).is_some());
  ///
  /// let [s1, s2] = r.full_match_capturing(msg).unwrap();
  /// assert_eq!(s1, "s");
  /// assert_eq!(s2, "f");
  /// // The result isn't copied, it points to the same memory:
  /// assert_eq!(s1.as_bytes().as_ptr(), msg[1..].as_bytes().as_ptr());
  /// assert_eq!(s2.as_bytes().as_ptr(), msg[3..].as_bytes().as_ptr());
  /// # Ok(())
  /// # }
  /// ```
  pub fn full_match_capturing<'a, const N: usize>(&self, text: &'a str) -> Option<[&'a str; N]> {
    self
      .full_match_capturing_view(StringView::from_str(text))
      .map(Self::convert_strings)
  }

  /// [`Self::partial_match()`] for arbitrary string encodings.
  pub fn partial_match_view(&self, text: StringView) -> bool {
    unsafe { self.0.partial_match(text.into_native()) }
  }

  /// Like [`Self::full_match()`], except that the pattern may match a substring
  /// of `text`.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a.df".parse()?;
  /// assert!(r.partial_match("asdf"));
  /// assert!(r.partial_match("asdfe"));
  /// assert!(r.partial_match("basdf"));
  /// assert!(!r.partial_match("ascf"));
  /// # Ok(())
  /// # }
  /// ```
  pub fn partial_match(&self, text: &str) -> bool {
    self.partial_match_view(StringView::from_str(text))
  }

  /// [`Self::partial_match_capturing()`] for arbitrary string encodings.
  pub fn partial_match_capturing_view<'a, const N: usize>(
    &self,
    text_view: StringView<'a>,
  ) -> Option<[StringView<'a>; N]> {
    if N == 0 {
      return if self.partial_match_view(text_view) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut argv: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.partial_match_n(
        text_view.into_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(argv.as_mut_ptr()),
        argv.len(),
      )
    } {
      return None;
    }

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  /// Match against `text` and return a subset of declared capture groups.
  ///
  /// Like [`Self::full_match_capturing()`], except that the pattern may match a
  /// substring of `text`.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::*;
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = RE2::compile("a(.+)d(f)".into(), o)?;
  /// assert_eq!(2, r.num_captures());
  ///
  /// let msg = "the asdf is withdfin me";
  /// // The 0 case still works, but just calls .partial_match():
  /// assert!(r.partial_match_capturing::<0>(msg).is_some());
  ///
  /// let [s1, s2] = r.partial_match_capturing(msg).unwrap();
  /// assert_eq!(s1, "sdf is with");
  /// assert_eq!(s2, "f");
  /// // The result isn't copied, it points to the same memory:
  /// assert_eq!(s1.as_bytes().as_ptr(), msg[5..].as_bytes().as_ptr());
  /// assert_eq!(s2.as_bytes().as_ptr(), msg[17..].as_bytes().as_ptr());
  /// # Ok(())
  /// # }
  /// ```
  pub fn partial_match_capturing<'a, const N: usize>(&self, text: &'a str) -> Option<[&'a str; N]> {
    self
      .partial_match_capturing_view(StringView::from_str(text))
      .map(Self::convert_strings)
  }

  /// [`Self::consume()`] for arbitrary string encodings.
  pub fn consume_view(&self, text_view: &mut StringView) -> bool {
    if !unsafe { self.0.consume(text_view.as_mut_native()) } {
      return false;
    }
    true
  }

  /// If the pattern matches some prefix of `text`, advance `text` past the
  /// match.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a.{2}".parse()?;
  /// let mut s = "asdf";
  /// assert!(r.consume(&mut s));
  /// assert_eq!(s, "f");
  /// # Ok(())
  /// # }
  /// ```
  pub fn consume(&self, text: &mut &str) -> bool {
    let mut text_view = StringView::from_str(text);
    let ret = self.consume_view(&mut text_view);
    if ret {
      *text = unsafe { text_view.as_str() };
    }
    ret
  }

  /// [`Self::consume_capturing()`] for arbitrary string encodings.
  pub fn consume_capturing_view<'a, const N: usize>(
    &self,
    text_view: &mut StringView<'a>,
  ) -> Option<[StringView<'a>; N]> {
    if N == 0 {
      return if self.consume_view(text_view) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut argv: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.consume_n(
        text_view.as_mut_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(argv.as_mut_ptr()),
        argv.len(),
      )
    } {
      return None;
    }

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  /// If the pattern matches some prefix of `text`, advance `text` past the
  /// match and return some subset of captured sub-patterns.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a(.)d(f)".parse()?;
  /// assert_eq!(2, r.num_captures());
  ///
  /// let mut msg = "asdfasdfe";
  /// // The 0 case still works, but just calls .consume():
  /// assert!(r.consume_capturing::<0>(&mut msg).is_some());
  /// assert_eq!(msg, "asdfe");
  ///
  /// let [s1, s2] = r.consume_capturing(&mut msg).unwrap();
  /// assert_eq!(s1, "s");
  /// assert_eq!(s2, "f");
  /// assert_eq!(msg, "e");
  /// # Ok(())
  /// # }
  /// ```
  pub fn consume_capturing<'a, const N: usize>(&self, text: &mut &'a str) -> Option<[&'a str; N]> {
    let mut text_view = StringView::from_str(text);
    let ret = self.consume_capturing_view(&mut text_view);
    if ret.is_some() {
      *text = unsafe { text_view.as_str() };
    }
    ret.map(Self::convert_strings)
  }

  /// [`Self::find_and_consume()`] for arbitrary string encodings.
  pub fn find_and_consume_view(&self, text_view: &mut StringView) -> bool {
    if !unsafe { self.0.find_and_consume(text_view.as_mut_native()) } {
      return false;
    }
    true
  }

  /// If the pattern matches anywhere in `text`, advance `text` past the match.
  ///
  /// Like [`Self::consume()`], but does not anchor the match at the beginning
  /// of the text.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a.{2}".parse()?;
  /// let mut s = "the asdf";
  /// assert!(r.find_and_consume(&mut s));
  /// assert_eq!(s, "f");
  /// # Ok(())
  /// # }
  /// ```
  pub fn find_and_consume(&self, text: &mut &str) -> bool {
    let mut text_view = StringView::from_str(text);
    let ret = self.find_and_consume_view(&mut text_view);
    if ret {
      *text = unsafe { text_view.as_str() };
    }
    ret
  }

  /// [`Self::find_and_consume_capturing()`] for arbitrary string encodings.
  pub fn find_and_consume_capturing_view<'a, const N: usize>(
    &self,
    text_view: &mut StringView<'a>,
  ) -> Option<[StringView<'a>; N]> {
    if N == 0 {
      return if self.find_and_consume_view(text_view) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut argv: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.find_and_consume_n(
        text_view.as_mut_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(argv.as_mut_ptr()),
        argv.len(),
      )
    } {
      return None;
    }

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  /// If the pattern matches anywhere in `text`, advance `text` past the match
  /// and return some subset of captured sub-patterns.
  ///
  /// Like [`Self::consume_capturing()`], but does not anchor the match at the
  /// beginning of the text.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a(.)d(f)".parse()?;
  /// assert_eq!(2, r.num_captures());
  ///
  /// let mut msg = "the asdf and the asdfe";
  /// // The 0 case still works, but just calls .find_and_consume():
  /// assert!(r.find_and_consume_capturing::<0>(&mut msg).is_some());
  /// assert_eq!(msg, " and the asdfe");
  ///
  /// let [s1, s2] = r.find_and_consume_capturing(&mut msg).unwrap();
  /// assert_eq!(s1, "s");
  /// assert_eq!(s2, "f");
  /// assert_eq!(msg, "e");
  /// # Ok(())
  /// # }
  /// ```
  pub fn find_and_consume_capturing<'a, const N: usize>(
    &self,
    text: &mut &'a str,
  ) -> Option<[&'a str; N]> {
    let mut text_view = StringView::from_str(text);
    let ret = self.find_and_consume_capturing_view(&mut text_view);
    if ret.is_some() {
      *text = unsafe { text_view.as_str() };
    }
    ret.map(Self::convert_strings)
  }

  /// [`Self::match_no_captures()`] for arbitrary string encodings.
  pub fn match_no_captures_view(
    &self,
    text: StringView,
    range: ops::Range<usize>,
    anchor: Anchor,
  ) -> bool {
    let ops::Range { start, end } = range;

    unsafe {
      self
        .0
        .match_single(text.into_native(), start, end, anchor.into_native())
    }
  }

  /// General matching routine. Suitable for calling from higher-level code.
  ///
  /// Match against `text` within `range`, taking into account `anchor`. Returns
  /// [`true`] if match found, [`false`] if not.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, options::Anchor};
  ///
  /// let r: RE2 = "(foo)|(bar)baz".parse()?;
  /// let msg = "barbazbla";
  ///
  /// assert!(r.match_no_captures(msg, 0..msg.len(), Anchor::Unanchored));
  /// assert!(r.match_no_captures(msg, 0..msg.len(), Anchor::AnchorStart));
  /// assert!(!r.match_no_captures(msg, 0..msg.len(), Anchor::AnchorBoth));
  /// assert!(r.match_no_captures(msg, 0..6, Anchor::AnchorBoth));
  /// assert!(!r.match_no_captures(msg, 1..msg.len(), Anchor::Unanchored));
  /// # Ok(())
  /// # }
  /// ```
  pub fn match_no_captures(&self, text: &str, range: ops::Range<usize>, anchor: Anchor) -> bool {
    self.match_no_captures_view(StringView::from_str(text), range, anchor)
  }

  /// [`Self::match_routine()`] for arbirary string encodings.
  pub fn match_routine_view<'a, const N: usize>(
    &self,
    text_view: StringView<'a>,
    range: ops::Range<usize>,
    anchor: Anchor,
  ) -> Option<[StringView<'a>; N]> {
    if N == 0 {
      return if self.match_no_captures_view(text_view, range, anchor) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    let ops::Range { start, end } = range;
    let mut submatches: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.match_routine(
        text_view.into_native(),
        start,
        end,
        anchor.into_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(submatches.as_mut_ptr()),
        submatches.len(),
      )
    } {
      return None;
    }

    Some(Self::convert_string_views(unsafe {
      array_assume_init(submatches)
    }))
  }

  /// General matching routine with capture groups. Suitable for calling from
  /// higher-level code.
  ///
  /// Match against `text` within `range`, taking into account `anchor`. Returns
  /// [`Some`] if match found, [`None`] if not.
  ///
  /// NB: Unlike other matching methods, the 0th element of the result
  /// corresponds to the entire matched text, so the indices of the returned
  /// array correspond to the indices of declared capture groups e.g. from
  /// [`Self::named_groups()`]. Also unlike other matching methods, requesting
  /// more captures than the number of declared capture groups will simply
  /// return empty strings for the excessive captures instead of failing the
  /// match.
  ///
  /// Performance-wise, `N == 0` (capturing nothing, like
  /// [`Self::match_no_captures()`]) is much faster than `N == 1` (only
  /// capturing the entire match text), which is faster than `N > 1` (if any
  /// capture groups are selected).
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, options::Anchor};
  ///
  /// let r: RE2 = "(foo)|(bar)baz".parse()?;
  /// let msg = "barbazbla";
  ///
  /// let [s0, s1, s2, s3] = r.match_routine(msg, 0..msg.len(), Anchor::AnchorStart).unwrap();
  /// assert_eq!(s0, "barbaz");
  /// assert_eq!(s1, "");
  /// assert_eq!(s2, "bar");
  /// assert_eq!(s3, "");
  /// # Ok(())
  /// # }
  /// ```
  pub fn match_routine<'a, const N: usize>(
    &self,
    text: &'a str,
    range: ops::Range<usize>,
    anchor: Anchor,
  ) -> Option<[&'a str; N]> {
    self
      .match_routine_view(StringView::from_str(text), range, anchor)
      .map(Self::convert_strings)
  }
}

/// String search and replace interface.
///
/// These methods use a mutable [`StringWrapper`] instance with dynamically
/// allocated data to record the result of applying a "rewrite string" to the
/// capture groups for a given match using [`Self::vector_rewrite()`]. They may
/// mutate data from the string or append to the string upon a successful match.
///
/// Within a rewrite string, backslash-escaped digits (`\1` to `\9`) can be
/// used to insert text matching corresponding parenthesized group
/// from the pattern. `\0` refers to the entire matched text:
///```
/// # fn main() -> Result<(), re2::RE2Error> {
/// use re2::{RE2, string::StringWrapper};
///
/// let r: RE2 = "b+".parse()?;
/// let mut s = StringWrapper::from_view("yabba dabba doo".into());
///
/// assert!(r.replace(&mut s, "d"));
/// assert_eq!("yada dabba doo", unsafe { s.as_view().as_str() });
///
/// assert!(r.replace(&mut s, r"!\0!"));
/// assert_eq!("yada da!bb!a doo", unsafe { s.as_view().as_str() });
/// # Ok(())
/// # }
/// ```
///
/// As with the matching interface, methods with a `*_view` suffix operate on
/// [`StringView`] instances, which may have arbitrary encodings.
impl RE2 {
  /// [`Self::replace()`] for arbitrary string encodings.
  pub fn replace_view(&self, text: &mut StringWrapper, rewrite: StringView) -> bool {
    unsafe { self.0.replace(text.as_mut_native(), rewrite.into_native()) }
  }

  /// Replace the first match of this pattern in `text` with `rewrite`.
  ///
  /// Returns [`true`] if the pattern matches and a replacement occurs,
  /// [`false`] otherwise.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = ".he".parse()?;
  /// let mut s = re2::string::StringWrapper::from_view("all the king's men".into());
  /// assert!(r.replace(&mut s, "duh"));
  /// assert_eq!(unsafe { s.as_view().as_str() }, "all duh king's men");
  /// # Ok(())
  /// # }
  /// ```
  pub fn replace(&self, text: &mut StringWrapper, rewrite: &str) -> bool {
    self.replace_view(text, StringView::from_str(rewrite))
  }

  /// [`Self::replace_n()`] for arbitrary string encodings.
  pub fn replace_n_view(
    &self,
    text: &mut StringWrapper,
    rewrite: StringView,
    limit: usize,
  ) -> usize {
    if limit == 0 {
      self.global_replace_view(text, rewrite)
    } else {
      let mut num_replacements_made: usize = 0;
      while self.replace_view(text, rewrite) {
        num_replacements_made += 1;
      }
      num_replacements_made
    }
  }

  /// Applies [`Self::replace()`] to `text` at most `limit` times. Returns the
  /// number of replacements made.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = ".he".parse()?;
  /// let mut s = re2::string::StringWrapper::from_view(
  ///   "all the king's horses and all the king's men".into());
  /// assert_eq!(2, r.replace_n(&mut s, "duh", 3));
  /// assert_eq!(
  ///   unsafe { s.as_view().as_str() },
  ///   "all duh king's horses and all duh king's men",
  /// );
  /// # Ok(())
  /// # }
  /// ```
  pub fn replace_n(&self, text: &mut StringWrapper, rewrite: &str, limit: usize) -> usize {
    self.replace_n_view(text, StringView::from_str(rewrite), limit)
  }

  /// [`Self::global_replace()`] for arbitrary string encodings.
  pub fn global_replace_view(&self, text: &mut StringWrapper, rewrite: StringView) -> usize {
    unsafe {
      self
        .0
        .global_replace(text.as_mut_native(), rewrite.into_native())
    }
  }

  /// Applies [`Self::replace()`] to `text` for all non-overlapping occurrences
  /// of the pattern. Returns the number of replacements made.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = ".he".parse()?;
  /// let mut s = re2::string::StringWrapper::from_view(
  ///   "all the king's horses and all the king's men".into());
  /// assert_eq!(2, r.global_replace(&mut s, "duh"));
  /// assert_eq!(
  ///   unsafe { s.as_view().as_str() },
  ///   "all duh king's horses and all duh king's men",
  /// );
  /// # Ok(())
  /// # }
  /// ```
  pub fn global_replace(&self, text: &mut StringWrapper, rewrite: &str) -> usize {
    self.global_replace_view(text, StringView::from_str(rewrite))
  }

  /// [`Self::extract()`] for arbitrary string encodings.
  pub fn extract_view(
    &self,
    text: StringView,
    rewrite: StringView,
    out: &mut StringWrapper,
  ) -> bool {
    unsafe {
      self.0.extract(
        text.into_native(),
        rewrite.into_native(),
        out.as_mut_native(),
      )
    }
  }

  /// Like [`Self::replace()`], except that if the pattern matches, `rewrite` is
  /// copied into `out` with substitutions. The non-matching portions of
  /// `text` are ignored.
  ///
  /// Returns [`true`] iff a match occured and the extraction happened
  /// successfully; if no match occurs, the string is left unaffected.
  ///
  /// **REQUIRES: `text` must not alias any part of `out`!**
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "(.h)e".parse()?;
  /// let mut s = re2::string::StringWrapper::blank();
  /// assert!(r.extract("all the king's men", r"\1a", &mut s));
  /// assert_eq!(unsafe { s.as_view().as_str() }, "tha");
  /// # Ok(())
  /// # }
  /// ```
  pub fn extract(&self, text: &str, rewrite: &str, out: &mut StringWrapper) -> bool {
    self.extract_view(
      StringView::from_str(text),
      StringView::from_str(rewrite),
      out,
    )
  }
}

/// High-level iterator adaptor interface.
///
/// These methods make use of lower-level matching methods like
/// [`Self::match_routine()`] to produce lazy streams of results.
///
/// As with the matching interface, methods with a `*_view` suffix operate on
/// [`StringView`] instances, which may have arbitrary encodings.
impl RE2 {
  /// [`Self::find_iter()`] for arbitrary string encodings.
  pub fn find_iter_view<'r, 'h: 'r, const N: usize>(
    &'r self,
    hay: StringView<'h>,
  ) -> impl Iterator<Item=[StringView<'h>; N]>+'r {
    assert_ne!(
      N, 0,
      "N must be at least 1 to capture the match text for non-overlapping matches"
    );
    MatchIter {
      remaining_input: hay,
      pattern: self,
    }
  }

  /// Yields all non-overlapping matches in `hay`. Supports capture groups.
  ///
  /// The `N` argument is interpreted the same way as in
  /// [`Self::match_routine()`], where requesting fewer submatches is more
  /// performant, and the 0th submatch corresponds to the entire matched text.
  /// However, note that `N` must be at least 1 when calling this method in
  /// order to record match boundaries to avoid overlaps.
  ///
  /// NB: if no input is consumed upon searching the regex, iteration will
  /// end to avoid looping infinitely.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a+(.)".parse()?;
  ///
  /// let hay = "aardvarks all ailing: awesome";
  /// let whole_matches: Vec<&str> = r.find_iter::<1>(hay).map(|[m]| m).collect();
  /// let submatches: Vec<&str> = r.find_iter::<2>(hay).map(|[_, m]| m).collect();
  /// assert_eq!(&whole_matches, &["aar", "ar", "al", "ai", "aw"]);
  /// assert_eq!(&submatches, &["r", "r", "l", "i", "w"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn find_iter<'r, 'h: 'r, const N: usize>(
    &'r self,
    hay: &'h str,
  ) -> impl Iterator<Item=[&'h str; N]>+'r {
    self
      .find_iter_view(StringView::from_str(hay))
      .map(Self::convert_strings)
  }

  /// [`Self::split()`] for arbitrary string encodings.
  pub fn split_view<'r, 'h: 'r>(
    &'r self,
    hay: StringView<'h>,
  ) -> impl Iterator<Item=StringView<'h>>+'r {
    SplitIter {
      remaining_input: Some(hay),
      pattern: self,
    }
  }

  /// Yields all slices between matches of the pattern.
  ///
  /// Split by arbitrary amount of tabs or whitespace:
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = r"[ \t]+".parse()?;
  ///
  /// let hay = "a b \t  c\td    e";
  /// let fields: Vec<&str> = r.split(hay).collect();
  /// assert_eq!(&fields, &["a", "b", "c", "d", "e"]);
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// Multiple contiguous matches yield empty slices:
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "X".parse()?;
  ///
  /// let hay = "XXXXaXXbXc";
  /// let chunks: Vec<&str> = r.split(hay).collect();
  /// assert_eq!(&chunks, &["", "", "", "", "a", "", "b", "c"]);
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// Separators at start or end also yield empty slices:
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "0".parse()?;
  ///
  /// let hay = "010";
  /// let chunks: Vec<&str> = r.split(hay).collect();
  /// assert_eq!(&chunks, &["", "1", ""]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn split<'r, 'h: 'r>(&'r self, hay: &'h str) -> impl Iterator<Item=&'h str>+'r {
    self
      .split_view(StringView::from_str(hay))
      .map(|s| unsafe { s.as_str() })
  }
}

/// Introspection methods to investigate match groups and rewrite strings.
impl RE2 {
  /// Returns the maximum submatch needed for the `rewrite` to be done by
  /// [`Self::replace()`]. E.g. if `rewrite == r"foo \2,\1"`, returns 2.
  ///
  /// [`Self::check_rewrite()`] ensures that this number is no larger than the
  /// result of [`Self::num_captures()`].
  ///```
  /// use re2::RE2;
  ///
  /// assert_eq!(0, RE2::max_submatch("asdf".into()));
  /// assert_eq!(0, RE2::max_submatch(r"\0asdf".into()));
  /// assert_eq!(1, RE2::max_submatch(r"\0a\1sdf".into()));
  /// assert_eq!(3, RE2::max_submatch(r"\3a\1sdf".into()));
  /// ```
  pub fn max_submatch(rewrite: StringView) -> usize {
    unsafe { re2_c::RE2Wrapper::max_submatch(rewrite.into_native()) }
  }

  /// Return the number of capture groups in the current pattern.
  ///
  /// Alternately, this can be understood as the highest capture group index
  /// which this pattern can support in a rewrite string, with 0 referring to
  /// the entire match. Also see [`Self::max_submatch()`].
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::RE2;
  ///
  /// assert_eq!(0, "a.df".parse::<RE2>()?.num_captures());
  /// assert_eq!(1, "a(.)df".parse::<RE2>()?.num_captures());
  /// assert_eq!(2, "a((.)df)".parse::<RE2>()?.num_captures());
  /// assert_eq!(3, "(?P<foo>a)((.)df)".parse::<RE2>()?.num_captures());
  /// # Ok(())
  /// # }
  /// ```
  pub fn num_captures(&self) -> usize { unsafe { self.0.num_captures() } }

  /// Return an FFI handle to a C++ iterator over the named capture groups.
  ///
  /// This method does not provide information about positional-only capture
  /// groups. Use [`Self::named_and_numbered_groups()`] for an iterator that
  /// covers positional as well as named groups.
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::RE2;
  ///
  /// assert_eq!(0, "a(.)df".parse::<RE2>()?.named_groups().count());
  /// assert_eq!(1, "a(?P<hey>.)df".parse::<RE2>()?.named_groups().count());
  ///
  /// // Not all captures are named:
  /// let r: RE2 = "a(?P<y>(?P<x>.)d(f)(?P<z>e))".parse()?;
  /// assert_eq!(4, r.num_captures());
  ///
  /// // Results are sorted by number:
  /// let groups: Vec<(&str, usize)> = r.named_groups()
  ///   .map(|g| (unsafe { g.name().as_str() }, *g.index()))
  ///   .collect();
  /// assert_eq!(vec![("y", 1), ("x", 2), ("z", 4)], groups);
  /// # Ok(())
  /// # }
  /// ```
  pub fn named_groups(&self) -> impl Iterator<Item=NamedGroup<'_>>+'_ { self.make_named_groups() }

  fn make_named_groups(&self) -> NamedCapturingGroups<'_> {
    unsafe { NamedCapturingGroups::from_native(self.0.named_groups()) }
  }

  /// Return an iterator covering both named and positional-only groups.
  ///
  /// Positional-only groups are represented with [`None`] instead of a
  /// [`StringView`].
  ///
  /// The index of each group can be recovered by calling `.enumerate()` on the
  /// result. This is possible because this iterator also generates a
  /// positional-only group at index 0, which can be thought
  /// of as corresponding to the 0th group in a rewrite string (aka the entire
  /// match).
  ///
  /// While most use cases will likely employ either only positional or only
  /// named groups, this method can be useful for introspection over
  /// uncontrolled inputs.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let r: re2::RE2 = "a(?P<y>(?P<x>.)d(f)(?P<z>e)(n))".parse()?;
  /// assert_eq!(5, r.num_captures());
  ///
  /// let indexed: Vec<(usize, Option<&str>)> = r.named_and_numbered_groups()
  ///   .map(|s| s.map(|s| unsafe { s.as_str() }))
  ///   .enumerate()
  ///   .collect();
  /// assert_eq!(
  ///   &indexed,
  ///   &[(0, None), (1, Some("y")), (2, Some("x")), (3, None), (4, Some("z")), (5, None)] );
  /// # Ok(())
  /// # }
  pub fn named_and_numbered_groups(
    &self,
  ) -> impl Iterator<Item=Option<StringView>>+ExactSizeIterator {
    NamedAndNumberedGroups::new(self.num_captures(), self.make_named_groups())
  }

  /// [`Self::check_rewrite()`] for arbitrary string encodings.
  pub fn check_rewrite_view(&self, rewrite: StringView) -> Result<(), RewriteError> {
    let mut sw = StringWrapper::blank();

    if unsafe {
      self
        .0
        .check_rewrite_string(rewrite.into_native(), sw.as_mut_native())
    } {
      Ok(())
    } else {
      Err(RewriteError {
        message: String::from_utf8_lossy(sw.as_view().as_slice()).to_string(),
      })
    }
  }

  /// Check that the given `rewrite` string is suitable for use with this
  /// regular expression.
  ///
  /// It checks that:
  /// - The regular expression has enough parenthesized subexpressions to
  ///   satisfy all of the `\N` tokens in rewrite
  /// - The rewrite string doesn't have any syntax errors.  E.g., `\` followed
  ///   by anything other than a digit or `\`.
  ///
  /// A [`true`] return value guarantees that [`Self::replace()`] and
  /// [`Self::extract()`] won't fail because of a bad rewrite string.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// use re2::{RE2, error::RewriteError};
  ///
  /// let r: RE2 = "asdf".parse()?;
  /// r.check_rewrite("a").unwrap();
  /// r.check_rewrite(r"a\0b").unwrap();
  /// assert_eq!(
  ///   RewriteError {
  ///     message: "Rewrite schema requests 1 matches, but the regexp only has 0 parenthesized subexpressions.".to_string(),
  ///   },
  ///   r.check_rewrite(r"a\0b\1").err().unwrap(),
  /// );
  /// # Ok(())
  /// # }
  /// ```
  pub fn check_rewrite(&self, rewrite: &str) -> Result<(), RewriteError> {
    self.check_rewrite_view(StringView::from_str(rewrite))
  }

  /// [`Self::vector_rewrite()`] for arbitrary string encodings.
  pub fn vector_rewrite_view<const N: usize>(
    &self,
    out: &mut StringWrapper,
    rewrite: StringView,
    inputs: [StringView; N],
  ) -> bool {
    let mut input_views: [MaybeUninit<re2_c::StringView>; N] = uninit_array();
    for (sv, s) in input_views.iter_mut().zip(inputs.into_iter()) {
      sv.write(s.into_native());
    }
    let input_views = unsafe { array_assume_init(input_views) };

    unsafe {
      self.0.vector_rewrite(
        out.as_mut_native(),
        rewrite.into_native(),
        input_views.as_ptr(),
        input_views.len(),
      )
    }
  }

  /// Append the `rewrite` string, with backslash substitutions from `inputs`,
  /// to string `out`.
  ///
  /// Returns [`true`] on success. This method can fail because of a malformed
  /// rewrite string. [`Self::check_rewrite()`] guarantees that the rewrite will
  /// be sucessful.
  ///
  ///```
  /// # fn main() -> Result<(), re2::RE2Error> {
  /// let mut sw = re2::string::StringWrapper::blank();
  /// let r: re2::RE2 = "a(s+)d(f+)".parse()?;
  /// assert!(r.vector_rewrite(&mut sw, r"bb\1cc\0dd\2", ["asdff", "s", "ff"]));
  /// assert_eq!(unsafe { sw.as_view().as_str() }, "bbsccasdffddff");
  /// # Ok(())
  /// # }
  /// ```
  pub fn vector_rewrite<const N: usize>(
    &self,
    out: &mut StringWrapper,
    rewrite: &str,
    inputs: [&str; N],
  ) -> bool {
    let rewrite = StringView::from_str(rewrite);
    let inputs = Self::convert_from_strings(inputs);
    self.vector_rewrite_view(out, rewrite, inputs)
  }
}

impl fmt::Debug for RE2 {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "RE2(pattern={:?}, options={:?})",
      self.pattern(),
      self.options()
    )
  }
}

impl fmt::Display for RE2 {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let o = self.options();
    if o == Options::default() {
      write!(f, "/{}/", self.pattern())
    } else {
      write!(f, "RE2(/{}/, options={:?})", self.pattern(), o)
    }
  }
}

impl cmp::PartialEq for RE2 {
  fn eq(&self, other: &Self) -> bool {
    self.pattern().eq(&other.pattern()) && self.options().eq(&other.options())
  }
}

impl cmp::Eq for RE2 {}

impl cmp::PartialOrd for RE2 {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl cmp::Ord for RE2 {
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    let intermediate = self.pattern().cmp(&other.pattern());
    if intermediate != cmp::Ordering::Equal {
      return intermediate;
    }
    self.options().cmp(&other.options())
  }
}

impl hash::Hash for RE2 {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.pattern().hash(state);
    self.options().hash(state);
  }
}

/// An FFI handle to a string-index pair representing a named parenthetical
/// capture group.
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct NamedGroup<'a> {
  inner: re2_c::NamedGroup,
  _ph: PhantomData<&'a u8>,
}

impl<'a> NamedGroup<'a> {
  pub(crate) const unsafe fn from_native(inner: re2_c::NamedGroup) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  /// Get a handle to the group's name, which can be decoded to
  /// [`str`](prim@str) if the original pattern was also UTF-8.
  pub const fn name(&self) -> StringView<'a> { StringView::from_native(self.inner.name_) }

  /// Get a handle to the index, which does not change after creation.
  pub const fn index(&self) -> &'a usize { unsafe { mem::transmute(&self.inner.index_) } }
}

impl<'a> fmt::Debug for NamedGroup<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "NamedGroup(i={}, name={:?})", self.index(), self.name())
  }
}

#[repr(transparent)]
struct NamedCapturingGroups<'a> {
  inner: re2_c::NamedCapturingGroups,
  _ph: PhantomData<&'a u8>,
}

impl<'a> NamedCapturingGroups<'a> {
  pub(crate) const unsafe fn from_native(inner: re2_c::NamedCapturingGroups) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  fn deref(&self) -> NamedGroup<'a> {
    let mut out: MaybeUninit<re2_c::NamedGroup> = MaybeUninit::uninit();
    unsafe {
      self.inner.deref(out.as_mut_ptr());
      NamedGroup::from_native(out.assume_init())
    }
  }

  fn advance(&mut self) {
    unsafe {
      self.inner.advance();
    }
  }

  fn completed(&self) -> bool { unsafe { self.inner.completed() } }
}

impl<'a> Iterator for NamedCapturingGroups<'a> {
  type Item = NamedGroup<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.completed() {
      return None;
    }

    let ret = self.deref();
    self.advance();
    Some(ret)
  }
}

struct NamedAndNumberedGroups<'a> {
  at_start: bool,
  total_num_captures: usize,
  groups_iter: Option<NamedCapturingGroups<'a>>,
  next_named_group: Option<NamedGroup<'a>>,
  cur_index: usize,
}

impl<'a> NamedAndNumberedGroups<'a> {
  pub fn new(total_num_captures: usize, groups_iter: NamedCapturingGroups<'a>) -> Self {
    Self {
      at_start: true,
      total_num_captures,
      groups_iter: Some(groups_iter),
      next_named_group: None,
      cur_index: 0,
    }
  }

  const fn remaining(&self) -> usize {
    if self.at_start {
      self.total_num_captures + 1
    } else {
      self.total_num_captures - self.cur_index + 1
    }
  }
}

impl<'a> Iterator for NamedAndNumberedGroups<'a> {
  type Item = Option<StringView<'a>>;

  fn next(&mut self) -> Option<Self::Item> {
    let Self {
      ref mut at_start,
      ref total_num_captures,
      ref mut groups_iter,
      ref mut next_named_group,
      ref mut cur_index,
    } = self;

    /* Return 0th submatch (for whole pattern). */
    if *at_start {
      *at_start = false;
      *cur_index = 1;
      return Some(None);
    }

    if *cur_index > *total_num_captures {
      return None;
    }

    if next_named_group.is_none() {
      let reset_groups_iter = if let Some(ref mut g) = groups_iter {
        if g.completed() {
          true
        } else {
          *next_named_group = Some(g.deref());
          g.advance();
          false
        }
      } else {
        false
      };
      if reset_groups_iter {
        *groups_iter = None;
      }
    }
    let ret = if let Some(named_group) = next_named_group {
      if *cur_index < *named_group.index() {
        None
      } else {
        debug_assert_eq!(cur_index, named_group.index());
        Some(named_group.name())
      }
    } else {
      None
    };
    if ret.is_some() {
      *next_named_group = None;
    }

    *cur_index += 1;

    Some(ret)
  }

  fn size_hint(&self) -> (usize, Option<usize>) { (self.remaining(), Some(self.remaining())) }
}

impl<'a> ExactSizeIterator for NamedAndNumberedGroups<'a> {}

struct MatchIter<'r, 'h, const N: usize> {
  remaining_input: StringView<'h>,
  pattern: &'r RE2,
}

impl<'r, 'h, const N: usize> Iterator for MatchIter<'r, 'h, N> {
  type Item = [StringView<'h>; N];

  fn next(&mut self) -> Option<Self::Item> {
    let matches = self.pattern.match_routine_view(
      self.remaining_input,
      0..self.remaining_input.len(),
      Anchor::Unanchored,
    )?;
    let consumed = unsafe {
      /* Group 0 has the entire match, and since we checked N > 0 elsewhere we know
       * it exists. */
      let full_match = matches.get_unchecked(0).as_slice();
      /* The remaining input should point past the end of the match. */
      let new_start = full_match.as_ptr().add(full_match.len());
      /* Calculate the distance from the previous start. */
      let consumed = new_start.offset_from(self.remaining_input.as_slice().as_ptr());
      debug_assert!(consumed >= 0);
      consumed as usize
    };
    /* Matched empty string; to avoid looping forever, return None. */
    if consumed == 0 {
      return None;
    }
    self.remaining_input = self.remaining_input.index_range(consumed..).unwrap();
    Some(matches)
  }
}

struct SplitIter<'r, 'h> {
  remaining_input: Option<StringView<'h>>,
  pattern: &'r RE2,
}

impl<'r, 'h> Iterator for SplitIter<'r, 'h> {
  type Item = StringView<'h>;

  fn next(&mut self) -> Option<Self::Item> {
    let remaining = self.remaining_input?;
    if let Some([m]) =
      self
        .pattern
        .match_routine_view(remaining, 0..remaining.len(), Anchor::Unanchored)
    {
      let m = m.as_slice();
      let prev_start = remaining.as_slice().as_ptr();
      let consumed = unsafe { m.as_ptr().offset_from(prev_start) };
      debug_assert!(consumed >= 0);
      let consumed = consumed as usize;
      let ret = remaining.index_range(..consumed).unwrap();
      let consumed_with_match = consumed + m.len();
      /* Matched empty string; to avoid looping forever, return None. */
      self.remaining_input = if consumed_with_match == 0 {
        None
      } else {
        Some(remaining.index_range(consumed_with_match..).unwrap())
      };
      Some(ret)
    } else {
      mem::take(&mut self.remaining_input)
    }
  }
}

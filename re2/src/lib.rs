/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

pub(crate) use re2_sys::{re2, re2_c};

pub mod error;
use error::{CompileError, RE2ErrorCode, RewriteError};

pub mod options;
use options::{Anchor, Options};

pub mod string;
use string::{StringView, StringWrapper};

pub mod set;

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

#[repr(transparent)]
pub struct NamedGroup<'a> {
  inner: re2_c::NamedGroup,
  _ph: PhantomData<&'a u8>,
}

impl<'a> NamedGroup<'a> {
  #[inline]
  pub(crate) const unsafe fn from_native(inner: re2_c::NamedGroup) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  #[inline]
  pub const fn name(&self) -> StringView<'a> {
    unsafe { StringView::from_native(self.inner.name_) }
  }

  #[inline]
  pub const fn index(&self) -> &'a usize { unsafe { mem::transmute(&self.inner.index_) } }
}

impl<'a> fmt::Debug for NamedGroup<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "NamedGroup(i={}, name={:?})", self.index(), self.name())
  }
}

#[repr(transparent)]
pub struct NamedCapturingGroups<'a> {
  inner: re2_c::NamedCapturingGroups,
  _ph: PhantomData<&'a u8>,
}

impl<'a> NamedCapturingGroups<'a> {
  #[inline]
  pub(crate) const unsafe fn from_native(inner: re2_c::NamedCapturingGroups) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  #[inline]
  fn deref(&self) -> NamedGroup<'a> {
    let mut out: MaybeUninit<re2_c::NamedGroup> = MaybeUninit::uninit();
    unsafe {
      self.inner.deref(out.as_mut_ptr());
      NamedGroup::from_native(out.assume_init())
    }
  }

  #[inline]
  fn advance(&mut self) {
    unsafe {
      self.inner.advance();
    }
  }

  #[inline]
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

#[repr(transparent)]
pub struct RE2(re2_c::RE2Wrapper);

impl RE2 {
  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// use re2::RE2;
  ///
  /// let q = RE2::quote_meta("1.5-1.8?".into());
  /// let r: RE2 = q.as_view().as_str().parse()?;
  /// assert_eq!(r"1\.5\-1\.8\?", r.pattern().as_str());
  /// assert!(r.full_match("1.5-1.8?"));
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn quote_meta(pattern: StringView<'_>) -> StringWrapper {
    let mut out = StringWrapper::from_view(pattern);
    unsafe { re2_c::RE2Wrapper::quote_meta(pattern.into_native(), out.as_mut_native()) };
    out
  }

  ///```
  /// use re2::RE2;
  ///
  /// assert_eq!(0, RE2::max_submatch("asdf".into()));
  /// assert_eq!(0, RE2::max_submatch(r"\0asdf".into()));
  /// assert_eq!(1, RE2::max_submatch(r"\0a\1sdf".into()));
  /// assert_eq!(3, RE2::max_submatch(r"\3a\1sdf".into()));
  /// ```
  #[inline]
  pub fn max_submatch(rewrite: StringView<'_>) -> usize {
    unsafe { re2_c::RE2Wrapper::max_submatch(rewrite.into_native()) }
  }

  #[inline]
  fn check_error_code(&self) -> Result<(), RE2ErrorCode> {
    RE2ErrorCode::from_native(unsafe { self.0.error_code() })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "asdf".parse()?;
  /// assert_eq!(r.pattern().as_str(), "asdf");
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn pattern(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.pattern()) } }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// use re2::{RE2, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = RE2::compile("asdf".into(), o)?;
  /// assert_eq!(o, r.options());
  /// assert_ne!(o, Options::default());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn options(&self) -> Options { unsafe { *self.0.options() }.into() }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
  #[inline]
  pub fn expensive_clone(&self) -> Self { Self::compile(self.pattern(), self.options()).unwrap() }

  #[inline]
  fn error(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.error()) } }

  #[inline]
  fn error_arg(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.error_arg()) } }

  fn check_error(&self) -> Result<(), CompileError> {
    self.check_error_code().map_err(|code| CompileError {
      message: self.error().as_str().to_string(),
      arg: self.error_arg().as_str().to_string(),
      code,
    })
  }

  pub fn compile(pattern: StringView<'_>, options: Options) -> Result<Self, CompileError> {
    let s = Self(unsafe { re2_c::RE2Wrapper::new(pattern.into_native(), &options.into_native()) });
    s.check_error()?;
    Ok(s)
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// use re2::RE2;
  ///
  /// assert_eq!(0, "a.df".parse::<RE2>()?.num_captures());
  /// assert_eq!(1, "a(.)df".parse::<RE2>()?.num_captures());
  /// assert_eq!(2, "a((.)df)".parse::<RE2>()?.num_captures());
  /// assert_eq!(3, "(?P<foo>a)((.)df)".parse::<RE2>()?.num_captures());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn num_captures(&self) -> usize { unsafe { self.0.num_captures() } }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
  ///   .map(|g| (g.name().as_str(), *g.index()))
  ///   .collect();
  /// assert_eq!(vec![("y", 1), ("x", 2), ("z", 4)], groups);
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn named_groups(&self) -> impl Iterator<Item=NamedGroup<'_>>+'_ {
    unsafe { NamedCapturingGroups::from_native(self.0.named_groups()) }
  }

  #[inline]
  fn empty_result<'a, const N: usize>() -> [&'a str; N] {
    assert_eq!(N, 0);
    let ret: [MaybeUninit<&'a str>; N] = uninit_array();
    unsafe { array_assume_init(ret) }
  }

  #[inline]
  unsafe fn convert_string_views<'a, const N: usize>(argv: [re2_c::StringView; N]) -> [&'a str; N] {
    let mut ret: [MaybeUninit<&'a str>; N] = uninit_array();
    for (output, input) in ret.iter_mut().zip(argv.into_iter()) {
      output.write(StringView::from_native(input).as_str());
    }
    array_assume_init(ret)
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "a.df".parse()?;
  /// assert!(r.full_match("asdf"));
  /// assert!(!r.full_match("asdfe"));
  /// assert!(!r.full_match("basdf"));
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn full_match(&self, text: &str) -> bool {
    let text = StringView::from_str(text);
    unsafe { self.0.full_match(text.into_native()) }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
    if N == 0 {
      return if self.full_match(text) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let text = StringView::from_str(text);
    let mut argv: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.full_match_n(
        text.into_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(argv.as_mut_ptr()),
        argv.len(),
      )
    } {
      return None;
    }

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "a.df".parse()?;
  /// assert!(r.partial_match("asdf"));
  /// assert!(r.partial_match("asdfe"));
  /// assert!(r.partial_match("basdf"));
  /// assert!(!r.partial_match("ascf"));
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn partial_match(&self, text: &str) -> bool {
    let text = StringView::from_str(text);
    unsafe { self.0.partial_match(text.into_native()) }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// use re2::{*, options::*};
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
    if N == 0 {
      return if self.partial_match(text) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let text = StringView::from_str(text);
    let mut argv: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.partial_match_n(
        text.into_native(),
        /* TODO: use MaybeUninit::slice_as_mut_ptr! */
        mem::transmute(argv.as_mut_ptr()),
        argv.len(),
      )
    } {
      return None;
    }

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "a.{2}".parse()?;
  /// let mut s = "asdf";
  /// assert!(r.consume(&mut s));
  /// assert_eq!(s, "f");
  /// # Ok(())
  /// # }
  /// ```
  pub fn consume(&self, text: &mut &str) -> bool {
    let mut text_view = StringView::from_str(text);
    if !unsafe { self.0.consume(text_view.as_mut_native()) } {
      return false;
    }
    *text = text_view.as_str();
    true
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
    if N == 0 {
      return if self.consume(text) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut text_view = StringView::from_str(text);
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

    *text = text_view.as_str();

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "a.{2}".parse()?;
  /// let mut s = "the asdf";
  /// assert!(r.find_and_consume(&mut s));
  /// assert_eq!(s, "f");
  /// # Ok(())
  /// # }
  /// ```
  pub fn find_and_consume(&self, text: &mut &str) -> bool {
    let mut text_view = StringView::from_str(text);
    if !unsafe { self.0.find_and_consume(text_view.as_mut_native()) } {
      return false;
    }
    *text = text_view.as_str();
    true
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
    if N == 0 {
      return if self.find_and_consume(text) {
        Some(Self::empty_result())
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut text_view = StringView::from_str(text);
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

    *text = text_view.as_str();

    Some(unsafe { Self::convert_string_views(array_assume_init(argv)) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = ".he".parse()?;
  /// let mut s = re2::string::StringWrapper::from_view("all the king's men".into());
  /// assert!(r.replace(&mut s, "duh"));
  /// assert_eq!(s.as_view().as_str(), "all duh king's men");
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn replace(&self, text: &mut StringWrapper, rewrite: &str) -> bool {
    let rewrite = StringView::from_str(rewrite);
    unsafe { self.0.replace(text.as_mut_native(), rewrite.into_native()) }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = ".he".parse()?;
  /// let mut s = re2::string::StringWrapper::from_view(
  ///   "all the king's horses and all the king's men".into());
  /// assert_eq!(2, r.global_replace(&mut s, "duh"));
  /// assert_eq!(
  ///   s.as_view().as_str(),
  ///   "all duh king's horses and all duh king's men",
  /// );
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn global_replace(&self, text: &mut StringWrapper, rewrite: &str) -> usize {
    let rewrite = StringView::from_str(rewrite);
    unsafe {
      self
        .0
        .global_replace(text.as_mut_native(), rewrite.into_native())
    }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "(.h)e".parse()?;
  /// let mut s = re2::string::StringWrapper::blank();
  /// assert!(r.extract("all the king's men", r"\1a", &mut s));
  /// assert_eq!(s.as_view().as_str(), "tha");
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn extract(&self, text: &str, rewrite: &str, out: &mut StringWrapper) -> bool {
    let text = StringView::from_str(text);
    let rewrite = StringView::from_str(rewrite);
    unsafe {
      self.0.extract(
        text.into_native(),
        rewrite.into_native(),
        out.as_mut_native(),
      )
    }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
    let text = StringView::from_str(text);
    let ops::Range { start, end } = range;

    unsafe {
      self
        .0
        .match_single(text.into_native(), start, end, anchor.into_native())
    }
  }

  /// **NB: The 0th element of the result is the entire match, so `::<0>`
  /// panics!**
  ///
  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
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
    assert_ne!(N, 0);
    let text = StringView::from_str(text);
    let ops::Range { start, end } = range;
    let mut submatches: [MaybeUninit<re2_c::StringView>; N] = uninit_array();

    if !unsafe {
      self.0.match_routine(
        text.into_native(),
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

    Some(unsafe { Self::convert_string_views(array_assume_init(submatches)) })
  }

  /// **NB: if no input is consumed upon searching the regex, iteration will
  /// end to avoid looping infinitely.**
  ///
  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "a+(.)".parse()?;
  ///
  /// let msg = "aardvarks all ailing: awesome";
  /// let whole_matches: Vec<&str> = r.find_iter::<1>(msg).map(|[m]| m).collect();
  /// let submatches: Vec<&str> = r.find_iter::<2>(msg).map(|[_, m]| m).collect();
  /// assert_eq!(&whole_matches, &["aar", "ar", "al", "ai", "aw"]);
  /// assert_eq!(&submatches, &["r", "r", "l", "i", "w"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn find_iter<'r, 'h: 'r, const N: usize>(
    &'r self,
    text: &'h str,
  ) -> impl Iterator<Item=[&'h str; N]>+'r {
    assert_ne!(N, 0);
    MatchIter {
      remaining_input: text,
      pattern: self,
    }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let r: re2::RE2 = "asdf".parse()?;
  /// r.check_rewrite_string("a").unwrap();
  /// r.check_rewrite_string(r"a\0b").unwrap();
  /// assert_eq!(
  ///   re2::error::RewriteError {
  ///     message: "Rewrite schema requests 1 matches, but the regexp only has 0 parenthesized subexpressions.".to_string(),
  ///   },
  ///   r.check_rewrite_string(r"a\0b\1").err().unwrap(),
  /// );
  /// # Ok(())
  /// # }
  /// ```
  pub fn check_rewrite_string(&self, rewrite: &str) -> Result<(), RewriteError> {
    let rewrite = StringView::from_str(rewrite);
    let mut sw = StringWrapper::blank();

    if unsafe {
      self
        .0
        .check_rewrite_string(rewrite.into_native(), sw.as_mut_native())
    } {
      Ok(())
    } else {
      Err(RewriteError {
        message: sw.as_view().as_str().to_string(),
      })
    }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::RE2Error> {
  /// let mut sw = re2::string::StringWrapper::blank();
  /// let r: re2::RE2 = "a(s+)d(f+)".parse()?;
  /// assert!(r.vector_rewrite(&mut sw, r"bb\1cc\0dd\2", ["asdff", "s", "ff"]));
  /// assert_eq!(sw.as_view().as_str(), "bbsccasdffddff");
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

    let mut input_views: [MaybeUninit<re2_c::StringView>; N] = uninit_array();
    for (sv, s) in input_views.iter_mut().zip(inputs.into_iter()) {
      sv.write(StringView::from_str(s).into_native());
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
}

impl ops::Drop for RE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

impl str::FromStr for RE2 {
  type Err = CompileError;

  ///```
  /// assert_eq!(
  ///   "a(sdf".parse::<re2::RE2>().err().unwrap(),
  ///   re2::error::CompileError {
  ///     message: "missing ): a(sdf".to_string(),
  ///     arg: "a(sdf".to_string(),
  ///     code: re2::error::RE2ErrorCode::MissingParen,
  ///   },
  /// );
  /// ```
  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Self::compile(StringView::from_str(s), Options::default())
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

struct MatchIter<'r, 'h, const N: usize> {
  remaining_input: &'h str,
  pattern: &'r RE2,
}

impl<'r, 'h, const N: usize> Iterator for MatchIter<'r, 'h, N> {
  type Item = [&'h str; N];

  fn next(&mut self) -> Option<Self::Item> {
    let matches = self.pattern.match_routine(
      self.remaining_input,
      0..self.remaining_input.len(),
      Anchor::Unanchored,
    )?;
    let consumed = unsafe {
      /* Group 0 has the entire match, and since we checked N > 0 elsewhere we know
       * it exists. */
      let full_match = matches.get_unchecked(0).as_bytes();
      /* The remaining input should point past the end of the match. */
      let new_start = full_match.as_ptr().add(full_match.len());
      /* Calculate the distance from the previous start. */
      let consumed = new_start.offset_from(self.remaining_input.as_bytes().as_ptr());
      debug_assert!(consumed >= 0);
      consumed as usize
    };
    /* Matched empty string; to avoid looping forever, return None. */
    if consumed == 0 {
      return None;
    }
    self.remaining_input = &self.remaining_input[consumed..];
    Some(matches)
  }
}

/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
#![feature(maybe_uninit_uninit_array)]
#![feature(maybe_uninit_array_assume_init)]
#![feature(const_maybe_uninit_uninit_array)]
#![feature(const_maybe_uninit_array_assume_init)]
#![feature(generic_const_exprs)]
#![feature(const_mut_refs)]
#![feature(const_slice_from_raw_parts_mut)]
#![feature(const_str_from_utf8_unchecked_mut)]
#![allow(incomplete_features)]

pub mod error;
pub use error::{CompileError, RE2ErrorCode, RewriteError};

pub mod options;
pub use options::{Anchor, CannedOptions, Encoding, Options};

pub mod string;
pub use string::{StringMut, StringView, StringWrapper};

#[allow(unused, improper_ctypes)]
mod bindings;
pub(crate) use bindings::root::{re2, re2_c_bindings as re2_c};

use std::{
  cmp, fmt, hash,
  marker::PhantomData,
  mem::{self, MaybeUninit},
  ops, str,
};

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
  /// use re2::*;
  ///
  /// let s = StringView::from_str("1.5-1.8?");
  /// let q = RE2::quote_meta(s);
  /// assert_eq!(q.as_view().as_str(), r"1\.5\-1\.8\?");
  /// ```
  #[inline]
  pub fn quote_meta(pattern: StringView<'_>) -> StringWrapper {
    let mut out = StringWrapper::from_view(pattern);
    unsafe { re2_c::RE2Wrapper::quote_meta(pattern.into_native(), out.as_mut_native()) };
    out
  }

  ///```
  /// use re2::*;
  ///
  /// assert_eq!(0, RE2::max_submatch(StringView::from_str("asdf")));
  /// assert_eq!(0, RE2::max_submatch(StringView::from_str(r"\0asdf")));
  /// assert_eq!(1, RE2::max_submatch(StringView::from_str(r"\0a\1sdf")));
  /// assert_eq!(3, RE2::max_submatch(StringView::from_str(r"\3a\1sdf")));
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
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("asdf")?;
  /// assert_eq!(r.pattern().as_str(), "asdf");
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn pattern(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.pattern()) } }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = RE2::compile(StringView::from_str("asdf"), o)?;
  /// assert_eq!(o, r.options());
  /// assert_ne!(o, Options::default());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn options(&self) -> Options { unsafe { *self.0.options() }.into() }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = RE2::compile(StringView::from_str("asdf"), o)?;
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

  ///```
  /// use re2::*;
  ///
  /// assert_eq!(
  ///   RE2::from_str("a(sdf").err().unwrap(),
  ///   CompileError {
  ///     message: "missing ): a(sdf".to_string(),
  ///     arg: "a(sdf".to_string(),
  ///     code: RE2ErrorCode::MissingParen,
  ///   },
  /// );
  /// ```
  pub fn from_str(pattern: &str) -> Result<Self, CompileError> {
    Self::compile(StringView::from_str(pattern), Options::default())
  }

  pub fn compile(pattern: StringView<'_>, options: Options) -> Result<Self, CompileError> {
    let s = Self(unsafe { re2_c::RE2Wrapper::new(pattern.into_native(), &options.into_native()) });
    s.check_error()?;
    Ok(s)
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::RE2;
  /// assert_eq!(0, RE2::from_str("a.df")?.num_captures());
  /// assert_eq!(1, RE2::from_str("a(.)df")?.num_captures());
  /// assert_eq!(2, RE2::from_str("a((.)df)")?.num_captures());
  /// assert_eq!(3, RE2::from_str("(?P<foo>a)((.)df)")?.num_captures());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn num_captures(&self) -> usize { unsafe { self.0.num_captures() } }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// assert_eq!(0, RE2::from_str("a(.)df")?.named_groups().count());
  /// assert_eq!(1, RE2::from_str("a(?P<hey>.)df")?.named_groups().count());
  ///
  /// // Not all captures are named:
  /// let r = RE2::from_str("a(?P<y>(?P<x>.)d(f)(?P<z>e))")?;
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

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a.df")?;
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

  #[inline]
  const unsafe fn empty_result<'a, const N: usize>() -> [&'a str; N] {
    let ret: [MaybeUninit<&'a str>; N] = MaybeUninit::uninit_array();
    MaybeUninit::array_assume_init(ret)
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a(.)d(f)")?;
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
        Some(unsafe { Self::empty_result() })
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let text = StringView::from_str(text);
    let mut argv = [StringView::empty().into_native(); N];

    if !unsafe {
      self
        .0
        .full_match_n(text.into_native(), argv.as_mut_ptr(), argv.len())
    } {
      return None;
    }

    let mut ret: [MaybeUninit<&'a str>; N] = MaybeUninit::uninit_array();
    for (output, input) in ret.iter_mut().zip(argv.into_iter()) {
      output.write(unsafe { StringView::from_native(input) }.as_str());
    }
    Some(unsafe { MaybeUninit::array_assume_init(ret) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a.df")?;
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
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let p = StringView::from_str("a(.+)d(f)");
  /// let r = RE2::compile(p, o)?;
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
        Some(unsafe { Self::empty_result() })
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let text = StringView::from_str(text);
    let mut argv = [StringView::empty().into_native(); N];

    if !unsafe {
      self
        .0
        .partial_match_n(text.into_native(), argv.as_mut_ptr(), argv.len())
    } {
      return None;
    }

    let mut ret: [MaybeUninit<&'a str>; N] = MaybeUninit::uninit_array();
    for (output, input) in ret.iter_mut().zip(argv.into_iter()) {
      output.write(unsafe { StringView::from_native(input) }.as_str());
    }
    Some(unsafe { MaybeUninit::array_assume_init(ret) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a.{2}")?;
  /// let mut s = "asdf";
  /// assert!(r.consume(&mut s));
  /// assert_eq!(s, "f");
  /// # Ok(())
  /// # }
  /// ```
  pub fn consume(&self, text: &mut &str) -> bool {
    let mut text_view = StringView::from_str(*text);
    if !unsafe { self.0.consume(text_view.as_mut_native()) } {
      return false;
    }
    *text = text_view.as_str();
    true
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a(.)d(f)")?;
  /// assert_eq!(2, r.num_captures());
  ///
  /// let mut msg = "asdfe";
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
        Some(unsafe { Self::empty_result() })
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut text_view = StringView::from_str(*text);
    let mut argv = [StringView::empty().into_native(); N];

    if !unsafe {
      self
        .0
        .consume_n(text_view.as_mut_native(), argv.as_mut_ptr(), argv.len())
    } {
      return None;
    }

    *text = text_view.as_str();

    let mut ret: [MaybeUninit<&'a str>; N] = MaybeUninit::uninit_array();
    for (output, input) in ret.iter_mut().zip(argv.into_iter()) {
      output.write(unsafe { StringView::from_native(input) }.as_str());
    }
    Some(unsafe { MaybeUninit::array_assume_init(ret) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a.{2}")?;
  /// let mut s = "the asdf";
  /// assert!(r.find_and_consume(&mut s));
  /// assert_eq!(s, "f");
  /// # Ok(())
  /// # }
  /// ```
  pub fn find_and_consume(&self, text: &mut &str) -> bool {
    let mut text_view = StringView::from_str(*text);
    if !unsafe { self.0.find_and_consume(text_view.as_mut_native()) } {
      return false;
    }
    *text = text_view.as_str();
    true
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::from_str("a(.)d(f)")?;
  /// assert_eq!(2, r.num_captures());
  ///
  /// let mut msg = "the asdfe";
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
        Some(unsafe { Self::empty_result() })
      } else {
        None
      };
    }
    if N > self.num_captures() {
      return None;
    }

    let mut text_view = StringView::from_str(*text);
    let mut argv = [StringView::empty().into_native(); N];

    if !unsafe {
      self
        .0
        .find_and_consume_n(text_view.as_mut_native(), argv.as_mut_ptr(), argv.len())
    } {
      return None;
    }

    *text = text_view.as_str();

    let mut ret: [MaybeUninit<&'a str>; N] = MaybeUninit::uninit_array();
    for (output, input) in ret.iter_mut().zip(argv.into_iter()) {
      output.write(unsafe { StringView::from_native(input) }.as_str());
    }
    Some(unsafe { MaybeUninit::array_assume_init(ret) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let r = RE2::from_str(".he")?;
  /// let mut s = StringWrapper::from_view(StringView::from_str("all the king's men"));
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
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let r = RE2::from_str(".he")?;
  /// let mut s = StringWrapper::from_view(StringView::from_str(
  ///   "all the king's horses and all the king's men"));
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
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let r = RE2::from_str("(.h)e")?;
  /// let mut s = StringWrapper::blank();
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
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let r = RE2::from_str("(foo)|(bar)baz")?;
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

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let r = RE2::from_str("(foo)|(bar)baz")?;
  /// let msg = "barbazbla";
  ///
  /// let [s0, s1, s2, s3] = r.match_routine::<3>(msg, 0..msg.len(), Anchor::AnchorStart).unwrap();
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
  ) -> Option<[&'a str; N + 1]> {
    let text = StringView::from_str(text);
    let ops::Range { start, end } = range;
    let mut submatches = [StringView::empty().into_native(); N + 1];

    if !unsafe {
      self.0.match_routine(
        text.into_native(),
        start,
        end,
        anchor.into_native(),
        submatches.as_mut_ptr(),
        submatches.len(),
      )
    } {
      return None;
    }

    let mut ret: [MaybeUninit<&'a str>; N + 1] = MaybeUninit::uninit_array();
    for (output, input) in ret.iter_mut().zip(submatches.into_iter()) {
      output.write(unsafe { StringView::from_native(input) }.as_str());
    }
    Some(unsafe { MaybeUninit::array_assume_init(ret) })
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let r = RE2::from_str("asdf")?;
  /// r.check_rewrite_string("a").unwrap();
  /// r.check_rewrite_string(r"a\0b").unwrap();
  /// assert_eq!(
  ///   RewriteError {
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
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let mut sw = StringWrapper::blank();
  /// let r = RE2::from_str("a(s+)d(f+)")?;
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

    let mut input_views = [StringView::empty().into_native(); N];
    for (sv, s) in input_views.iter_mut().zip(inputs.into_iter()) {
      *sv = StringView::from_str(s).into_native();
    }

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
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    let intermediate = self.pattern().partial_cmp(&other.pattern());
    if intermediate != Some(cmp::Ordering::Equal) {
      return intermediate;
    }
    self.options().partial_cmp(&other.options())
  }
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

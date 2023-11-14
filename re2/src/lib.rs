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

#[allow(unused, improper_ctypes)]
mod bindings;

pub mod error;
use error::{CompileError, RE2ErrorCode};

pub mod options;
use options::Options;

pub(crate) use bindings::root::{re2, re2_c_bindings as re2_c};

use std::{
  cmp, fmt, hash,
  marker::PhantomData,
  mem::{self, MaybeUninit},
  num::NonZeroUsize,
  ops,
  os::raw::c_char,
  ptr, slice, str,
};


///```
/// use re2::StringView;
///
/// let s = StringView::from_str("asdf");
/// assert_eq!(s.as_str(), "asdf");
/// assert_eq!(StringView::empty().as_str(), "");
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct StringView<'a> {
  inner: re2_c::StringView,
  _ph: PhantomData<&'a u8>,
}

impl<'a> StringView<'a> {
  #[inline]
  pub const fn empty() -> Self {
    let inner = re2_c::StringView {
      data_: ptr::null(),
      len_: 0,
    };
    unsafe { Self::from_native(inner) }
  }

  #[inline]
  pub(crate) const unsafe fn from_native(inner: re2_c::StringView) -> Self {
    Self {
      inner,
      _ph: PhantomData,
    }
  }

  #[inline]
  pub(crate) const fn into_native(self) -> re2_c::StringView { self.inner }

  #[inline]
  pub const fn from_slice(b: &'a [u8]) -> Self {
    let inner = re2_c::StringView {
      data_: b.as_ptr() as *const c_char,
      len_: b.len(),
    };
    unsafe { Self::from_native(inner) }
  }

  #[inline]
  pub const fn from_str(s: &'a str) -> Self { Self::from_slice(s.as_bytes()) }

  #[inline]
  const unsafe fn data_pointer(&self) -> *const u8 { mem::transmute(self.inner.data_) }

  #[inline]
  pub const fn len(&self) -> usize { self.inner.len_ }

  #[inline]
  pub const fn as_slice(&self) -> &'a [u8] {
    unsafe { slice::from_raw_parts(self.data_pointer(), self.len()) }
  }

  #[inline]
  pub const fn as_str(&self) -> &'a str { unsafe { str::from_utf8_unchecked(self.as_slice()) } }
}

impl<'a> AsMut<re2_c::StringView> for StringView<'a> {
  fn as_mut(&mut self) -> &mut re2_c::StringView { &mut self.inner }
}

impl<'a> Default for StringView<'a> {
  fn default() -> Self { Self::empty() }
}

impl<'a> fmt::Debug for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{:?}", self.as_str()) }
}

impl<'a> fmt::Display for StringView<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
}

impl<'a> cmp::PartialEq for StringView<'a> {
  fn eq(&self, other: &Self) -> bool { self.as_slice().eq(other.as_slice()) }
}

impl<'a> cmp::Eq for StringView<'a> {}

impl<'a> cmp::PartialOrd for StringView<'a> {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    self.as_slice().partial_cmp(other.as_slice())
  }
}

impl<'a> cmp::Ord for StringView<'a> {
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_slice().cmp(other.as_slice()) }
}

impl<'a> hash::Hash for StringView<'a> {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.as_slice().hash(state);
  }
}

///```
/// use re2::*;
///
/// let s = StringWrapper::from_view(StringView::from_str("asdf"));
/// assert_eq!(s.as_view().as_str(), "asdf");
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct StringWrapper(re2_c::StringWrapper);

impl StringWrapper {
  ///```
  /// let s = re2::StringWrapper::blank();
  /// assert_eq!(s.as_view().as_str(), "");
  /// ```
  #[inline]
  pub fn blank() -> Self { Self(unsafe { re2_c::StringWrapper::new() }) }

  #[inline]
  pub fn from_view(s: StringView<'_>) -> Self {
    Self(unsafe { re2_c::StringWrapper::new1(s.into_native()) })
  }

  #[inline]
  pub(crate) fn as_mut_native(&mut self) -> &mut re2_c::StringWrapper { &mut self.0 }

  #[inline]
  pub fn as_view(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.as_view()) } }
}

impl ops::Drop for StringWrapper {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
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
  pub const fn index(&self) -> &usize { &self.inner.index_ }
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
  pub fn deref(&self) -> NamedGroup<'a> {
    let mut out: MaybeUninit<re2_c::NamedGroup> = MaybeUninit::uninit();
    unsafe {
      self.inner.deref(out.as_mut_ptr());
      NamedGroup::from_native(out.assume_init())
    }
  }

  #[inline]
  pub fn advance(&mut self) {
    unsafe {
      self.inner.advance();
    }
  }

  #[inline]
  pub fn completed(&self) -> bool { unsafe { self.inner.completed() } }
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
  pub fn quote_meta(pattern: StringView<'_>) -> StringWrapper {
    let mut out = StringWrapper::blank();
    unsafe { re2_c::RE2Wrapper::quote_meta(pattern.into_native(), out.as_mut_native()) };
    out
  }

  #[inline]
  fn check_error_code(&self) -> Result<(), RE2ErrorCode> {
    RE2ErrorCode::from_native(unsafe { self.0.error_code() })
  }

  #[inline]
  pub fn pattern(&self) -> StringView<'_> { unsafe { StringView::from_native(self.0.pattern()) } }

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
  /// use re2::{*, error::*};
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
  /// let r = RE2::from_str("a(?P<y>(?P<x>.)d(f))")?;
  /// assert_eq!(3, r.num_captures());
  /// let groups: Vec<(&str, usize)> = r.named_groups()
  ///   .map(|g| (g.name().as_str(), *g.index()))
  ///   .collect();
  /// assert_eq!(vec![("x", 2), ("y", 1)], groups);
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
        .full_match_n(text.into_native(), argv.as_mut_ptr(), N)
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
  /// use re2::{*, options::*};
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
        .partial_match_n(text.into_native(), argv.as_mut_ptr(), N)
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
    let ret = unsafe { self.0.consume(text_view.as_mut()) };
    *text = text_view.as_str();
    ret
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

    if !unsafe { self.0.consume_n(text_view.as_mut(), argv.as_mut_ptr(), N) } {
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
    let ret = unsafe { self.0.find_and_consume(text_view.as_mut()) };
    *text = text_view.as_str();
    ret
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
        .find_and_consume_n(text_view.as_mut(), argv.as_mut_ptr(), N)
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
  /// assert_eq!(2, r.global_replace(&mut s, "duh").unwrap().get());
  /// assert_eq!(
  ///   s.as_view().as_str(),
  ///   "all duh king's horses and all duh king's men",
  /// );
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn global_replace(&self, text: &mut StringWrapper, rewrite: &str) -> Option<NonZeroUsize> {
    let rewrite = StringView::from_str(rewrite);
    NonZeroUsize::new(unsafe {
      self
        .0
        .global_replace(text.as_mut_native(), rewrite.into_native())
    })
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
}

impl ops::Drop for RE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

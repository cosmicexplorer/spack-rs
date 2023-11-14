/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

#[allow(unused, improper_ctypes)]
mod bindings;

pub mod error;
use error::{CompileError, RE2ErrorCode};

pub mod options;
use options::Options;

pub(crate) use bindings::root::{re2, re2_c_bindings as re2_c};

use indexmap::IndexMap;

use std::{
  cmp, fmt, hash,
  marker::PhantomData,
  mem,
  os::raw::{c_char, c_void},
  ptr, slice, str,
};


///```
/// use re2::StringView;
///
/// let s = StringView::from_str("asdf");
/// assert_eq!(s.as_str(), "asdf");
/// assert_eq!(StringView::empty().as_str(), "");
///```
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
  pub const fn from_slice(b: &'a [u8]) -> Self {
    let inner = re2_c::StringView {
      data_: unsafe { mem::transmute(b.as_ptr()) },
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

/* ///``` */
/* /// let s = re2::StringWrapper::new("asdf"); */
/* /// assert!(!s.is_empty()); */
/* /// assert_eq!(4, s.len()); */
/* /// // FIXME: BROKEN!!! */
/* /// // assert_eq!(s.as_str(), "asdf"); */
/* /// ``` */
/* #[repr(transparent)] */
/* pub struct StringWrapper(pub re2::StringWrapper); */

/* impl StringWrapper { */
/* ///``` */
/* /// let s = re2::StringWrapper::blank(); */
/* /// assert!(s.is_empty()); */
/* /// assert_eq!(s.as_str(), ""); */
/* /// ``` */
/* #[inline] */
/* pub fn blank() -> Self { Self(unsafe { re2::StringWrapper::new() }) } */

/* #[inline] */
/* pub fn new(s: &str) -> Self { */
/* let s: re2_string_view = StringView::from_str(s).into(); */
/* Self(unsafe { re2::StringWrapper::new1(s) }) */
/* } */

/* #[inline] */
/* pub fn is_empty(&self) -> bool { unsafe { self.0.empty() } } */

/* #[inline] */
/* pub fn len(&self) -> usize { unsafe { self.0.size() } } */

/* #[inline] */
/* pub fn as_str(&self) -> &str { */
/* let sv: StringView<'_> = unsafe { self.0.view() }.into(); */
/* sv.as_str() */
/* } */
/* } */

/* impl AsMut<re2_string> for StringWrapper { */
/* fn as_mut(&mut self) -> &mut re2_string { unsafe {
 * mem::transmute(self.0.get_mutable()) } } */
/* } */

/* /\* FIXME: why does this SIGSEGV???? *\/ */
/* /\* impl ops::Drop for StringWrapper { *\/ */
/* /\* fn drop(&mut self) { *\/ */
/* /\* unsafe { *\/ */
/* /\* self.0.destruct(); *\/ */
/* /\* } *\/ */
/* /\* } *\/ */
/* /\* } *\/ */

/* #[repr(transparent)] */
/* pub struct NamedGroup<'a> { */
/* pub inner: re2::NamedGroup, */
/* _ph: PhantomData<&'a u8>, */
/* } */

/* impl<'a> NamedGroup<'a> { */
/* #[inline] */
/* pub fn name(&self) -> StringView<'a> { self.inner.name.into() } */

/* #[inline] */
/* pub fn index(&self) -> usize { self.inner.index } */
/* } */

/* #[repr(transparent)] */
/* pub struct GroupNames<'a> { */
/* pub inner: re2::GroupNames, */
/* _ph: PhantomData<&'a u8>, */
/* } */

/* impl<'a> GroupNames<'a> { */
/* #[inline] */
/* pub const unsafe fn from_native(inner: re2::GroupNames) -> Self { */
/* Self { */
/* inner, */
/* _ph: PhantomData, */
/* } */
/* } */

/* #[inline] */
/* pub fn len(&self) -> usize { unsafe { self.inner.size() } } */

/* #[inline] */
/* pub fn get_name(&self, i: usize) -> Option<&NamedGroup<'a>> { */
/* if i >= self.len() { */
/* return None; */
/* } */
/* let g: &NamedGroup<'a> = unsafe { mem::transmute(self.inner.at(i)) }; */
/* Some(g) */
/* } */

/* pub fn into_mapping(&self) -> IndexMap<&'a str, usize> { */
/* (0..self.len()) */
/* .map(|i| { */
/* self */
/* .get_name(i) */
/* .map(|g| (g.name().as_str(), g.index())) */
/* .unwrap() */
/* }) */
/* .collect() */
/* } */
/* } */

/* /\* FIXME: why does this SIGSEGV???? *\/ */
/* /\* impl ops::Drop for GroupNames { *\/ */
/* /\* fn drop(&mut self) { *\/ */
/* /\* unsafe { *\/ */
/* /\* self.0.destruct(); *\/ */
/* /\* } *\/ */
/* /\* } *\/ */
/* /\* } *\/ */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// use re2::{RE2, error::*}; */
/* /// */
/* /// let r = RE2::new(".he")?; */
/* /// assert!(r.full_match("the")); */
/* /// assert!(!r.partial_match("hello")); */
/* /// assert!(r.partial_match("othello")); */
/* /// assert!(r.partial_match("the")); */
/* /// */
/* /// assert_eq!( */
/* ///   RE2::new("as(df").err().unwrap(), */
/* ///   CompileError { */
/* ///     message: "missing ): as(df".to_string(), */
/* ///     arg: "as(df".to_string(), */
/* ///     code: RE2ErrorCode::MissingParen, */
/* ///   }, */
/* /// ); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* #[repr(transparent)] */
/* pub struct RE2(pub re2::RE2); */

/* impl RE2 { */
/* #[inline] */
/* fn parse_string_view<'a>(s: re2_string_view) -> &'a str { */
/* let s: StringView<'a> = s.into(); */
/* s.as_str() */
/* } */

/* fn check_error_code(&self) -> Result<(), RE2ErrorCode> { */
/* RE2ErrorCode::from_native(self.0.error_code_()) */
/* } */

/* fn error(&self) -> &str { Self::parse_string_view(unsafe {
 * self.0.error_view() }) } */

/* fn error_arg(&self) -> &str { Self::parse_string_view(unsafe {
 * self.0.error_arg_view() }) } */

/* fn check_error_state(&self) -> Result<(), CompileError> { */
/* self.check_error_code().map_err(|code| { */
/* let message = self.error().to_string(); */
/* let arg = self.error_arg().to_string(); */
/* CompileError { message, arg, code } */
/* }) */
/* } */

/* pub fn new(pattern: impl AsRef<str>) -> Result<Self, CompileError> { */
/* let pattern = StringView::from_str(pattern.as_ref()); */
/* let ret = Self(unsafe { re2::RE2::new2(pattern.into()) }); */
/* ret.check_error_state()?; */
/* Ok(ret) */
/* } */

/* pub fn new_with_options( */
/* pattern: impl AsRef<str>, */
/* options: Options, */
/* ) -> Result<Self, CompileError> { */
/* let pattern = StringView::from_str(pattern.as_ref()); */
/* let ret = Self(unsafe { re2::RE2::new3(pattern.into(),
 * &options.into_native()) }); */
/* ret.check_error_state()?; */
/* Ok(ret) */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// use re2::{*, options::*}; */
/* /// */
/* /// let o: Options = CannedOptions::POSIX.into(); */
/* /// let r = RE2::new_with_options(".he", o)?; */
/* /// assert_eq!(o, r.options()); */
/* /// assert_ne!(o, Options::default()); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* #[inline] */
/* pub fn options(&self) -> Options { self.0.options_.into() } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new(".he")?; */
/* /// assert_eq!(".he", r.pattern()); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* #[inline] */
/* pub fn pattern(&self) -> &str { Self::parse_string_view(unsafe {
 * self.0.pattern_view() }) } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new(".he")?; */
/* /// assert_eq!(0, r.num_captures()); */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// assert_eq!(1, r.num_captures()); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* #[inline] */
/* pub fn num_captures(&self) -> usize { self.0.num_captures_ as usize } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("asdf")?; */
/* /// assert_eq!(0, r.num_captures()); */
/* /// assert_eq!(0, r.named_groups().len()); */
/* /// */
/* /// let r = re2::RE2::new("(?P<foo>.+) bla")?; */
/* /// assert_eq!(1, r.num_captures()); */
/* /// // let g = r.named_groups(); */
/* /// // assert_eq!(1, g.len()); */
/* /// // assert_eq!("foo", g.get_name(0).unwrap().as_str()); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* #[inline] */
/* pub fn named_groups(&self) -> GroupNames<'_> { */
/* unsafe { GroupNames::from_native(re2::GroupNames::new(&self.0)) } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new(".he")?; */
/* /// assert_eq!(r, r.expensive_clone()); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn expensive_clone(&self) -> Self { */
/* Self::new_with_options(self.pattern(), self.options()).unwrap() */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new(".he")?; */
/* /// assert!(r.full_match("the")); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* #[inline] */
/* pub fn full_match(&self, text: &str) -> bool { */
/* let text = StringView::from_str(text); */
/* unsafe { re2::RE2_FullMatchN(text.into(), &self.0, ptr::null(), 0) } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// assert_eq!(1, r.num_captures()); */
/* /// let [s] = r.full_match_capturing("the").unwrap(); */
/* /// assert_eq!(s, "th"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn full_match_capturing<'a, const N: usize>(&self, text: &'a str) ->
 * Option<[&'a str; N]> { */
/* if N > self.num_captures() { */
/* return None; */
/* } */
/* let mut args: [mem::MaybeUninit<&'a str>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* let argv: [re2::RE2_Arg; N] = { */
/* let mut argv: [mem::MaybeUninit<re2::RE2_Arg>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in args.iter_mut().zip(argv.iter_mut()) { */
/* arg.write(re2::RE2_Arg { */
/* arg_: a.as_mut_ptr() as usize as *mut c_void, */
/* parser_: Some(parse_str), */
/* }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv) } */
/* }; */
/* let argv_ref: [*const re2::RE2_Arg; N] = { */
/* let mut argv_ref: [mem::MaybeUninit<*const re2::RE2_Arg>; N] = */
/* mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in argv.iter().zip(argv_ref.iter_mut()) { */
/* arg.write(unsafe { mem::transmute(a) }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv_ref) } */
/* }; */

/* if unsafe { */
/* re2::RE2_FullMatchN( */
/* StringView::from_str(text).into(), */
/* &self.0, */
/* argv_ref.as_ptr(), */
/* argv_ref.len() as i32, */
/* ) */
/* } { */
/* Some(unsafe { mem::MaybeUninit::array_assume_init(args) }) */
/* } else { */
/* None */
/* } */
/* } */

/* #[inline] */
/* pub fn partial_match(&self, text: &str) -> bool { */
/* let text = StringView::from_str(text); */
/* unsafe { re2::RE2_PartialMatchN(text.into(), &self.0, ptr::null(), 0) } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// assert_eq!(1, r.num_captures()); */
/* /// let [s] = r.partial_match_capturing("othello").unwrap(); */
/* /// assert_eq!(s, "th"); */
/* /// */
/* /// // Ensure it uses the same memory (no copying): */
/* /// let data = "this is the source string"; */
/* /// let [s] = r.partial_match_capturing(data).unwrap(); */
/* /// assert_eq!(s, "th"); */
/* /// assert_eq!(s.as_bytes().as_ptr(), data[8..].as_bytes().as_ptr()); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn partial_match_capturing<'a, const N: usize>(&self, text: &'a str)
 * -> Option<[&'a str; N]> { */
/* if N > self.num_captures() { */
/* return None; */
/* } */
/* let mut args: [mem::MaybeUninit<&'a str>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* let argv: [re2::RE2_Arg; N] = { */
/* let mut argv: [mem::MaybeUninit<re2::RE2_Arg>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in args.iter_mut().zip(argv.iter_mut()) { */
/* arg.write(re2::RE2_Arg { */
/* arg_: a.as_mut_ptr() as usize as *mut c_void, */
/* parser_: Some(parse_str), */
/* }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv) } */
/* }; */
/* let argv_ref: [*const re2::RE2_Arg; N] = { */
/* let mut argv_ref: [mem::MaybeUninit<*const re2::RE2_Arg>; N] = */
/* mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in argv.iter().zip(argv_ref.iter_mut()) { */
/* arg.write(unsafe { mem::transmute(a) }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv_ref) } */
/* }; */

/* if unsafe { */
/* re2::RE2_PartialMatchN( */
/* StringView::from_str(text).into(), */
/* &self.0, */
/* argv_ref.as_ptr(), */
/* argv_ref.len() as i32, */
/* ) */
/* } { */
/* Some(unsafe { mem::MaybeUninit::array_assume_init(args) }) */
/* } else { */
/* None */
/* } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// let mut s = "the king's men"; */
/* /// assert!(r.consume(&mut s)); */
/* /// assert_eq!(s, " king's men"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn consume(&self, text: &mut &str) -> bool { */
/* let mut text_arg: re2_string_view = StringView::from_str(*text).into(); */
/* if unsafe { re2::RE2_ConsumeN(&mut text_arg, &self.0, ptr::null(), 0) } { */
/* let text_arg: StringView<'_> = text_arg.into(); */
/* *text = text_arg.as_str(); */
/* true */
/* } else { */
/* false */
/* } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// let mut s = "the king's men"; */
/* /// let [s1] = r.consume_capturing(&mut s).unwrap(); */
/* /// assert_eq!(s1, "th"); */
/* /// assert_eq!(s, " king's men"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn consume_capturing<'a, const N: usize>(&self, text: &mut &'a str) ->
 * Option<[&'a str; N]> { */
/* if N > self.num_captures() { */
/* return None; */
/* } */
/* let mut args: [mem::MaybeUninit<&'a str>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* let argv: [re2::RE2_Arg; N] = { */
/* let mut argv: [mem::MaybeUninit<re2::RE2_Arg>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in args.iter_mut().zip(argv.iter_mut()) { */
/* arg.write(re2::RE2_Arg { */
/* arg_: a.as_mut_ptr() as usize as *mut c_void, */
/* parser_: Some(parse_str), */
/* }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv) } */
/* }; */
/* let argv_ref: [*const re2::RE2_Arg; N] = { */
/* let mut argv_ref: [mem::MaybeUninit<*const re2::RE2_Arg>; N] = */
/* mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in argv.iter().zip(argv_ref.iter_mut()) { */
/* arg.write(unsafe { mem::transmute(a) }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv_ref) } */
/* }; */

/* let mut text_arg: re2_string_view = StringView::from_str(*text).into(); */
/* if unsafe { */
/* re2::RE2_ConsumeN( */
/* &mut text_arg, */
/* &self.0, */
/* argv_ref.as_ptr(), */
/* argv_ref.len() as i32, */
/* ) */
/* } { */
/* let text_arg: StringView<'_> = text_arg.into(); */
/* *text = text_arg.as_str(); */
/* Some(unsafe { mem::MaybeUninit::array_assume_init(args) }) */
/* } else { */
/* None */
/* } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// let mut s = "all of the king's men"; */
/* /// assert!(r.find_and_consume(&mut s)); */
/* /// assert_eq!(s, " king's men"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn find_and_consume(&self, text: &mut &str) -> bool { */
/* let mut text_arg: re2_string_view = StringView::from_str(*text).into(); */
/* if unsafe { re2::RE2_FindAndConsumeN(&mut text_arg, &self.0, ptr::null(),
 * 0) } { */
/* let text_arg: StringView<'_> = text_arg.into(); */
/* *text = text_arg.as_str(); */
/* true */
/* } else { */
/* false */
/* } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// let r = re2::RE2::new("(.h)e")?; */
/* /// let mut s = "all of the king's men"; */
/* /// let [s1] = r.find_and_consume_capturing(&mut s).unwrap(); */
/* /// assert_eq!(s1, "th"); */
/* /// assert_eq!(s, " king's men"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn find_and_consume_capturing<'a, const N: usize>( */
/* &self, */
/* text: &mut &'a str, */
/* ) -> Option<[&'a str; N]> { */
/* if N > self.num_captures() { */
/* return None; */
/* } */
/* let mut args: [mem::MaybeUninit<&'a str>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* let argv: [re2::RE2_Arg; N] = { */
/* let mut argv: [mem::MaybeUninit<re2::RE2_Arg>; N] =
 * mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in args.iter_mut().zip(argv.iter_mut()) { */
/* arg.write(re2::RE2_Arg { */
/* arg_: a.as_mut_ptr() as usize as *mut c_void, */
/* parser_: Some(parse_str), */
/* }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv) } */
/* }; */
/* let argv_ref: [*const re2::RE2_Arg; N] = { */
/* let mut argv_ref: [mem::MaybeUninit<*const re2::RE2_Arg>; N] = */
/* mem::MaybeUninit::uninit_array(); */
/* for (a, arg) in argv.iter().zip(argv_ref.iter_mut()) { */
/* arg.write(unsafe { mem::transmute(a) }); */
/* } */
/* unsafe { mem::MaybeUninit::array_assume_init(argv_ref) } */
/* }; */

/* let mut text_arg: re2_string_view = StringView::from_str(*text).into(); */
/* if unsafe { */
/* re2::RE2_FindAndConsumeN( */
/* &mut text_arg, */
/* &self.0, */
/* argv_ref.as_ptr(), */
/* argv_ref.len() as i32, */
/* ) */
/* } { */
/* let text_arg: StringView<'_> = text_arg.into(); */
/* *text = text_arg.as_str(); */
/* Some(unsafe { mem::MaybeUninit::array_assume_init(args) }) */
/* } else { */
/* None */
/* } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// use re2::*; */
/* /// */
/* /// let r = RE2::new(".he")?; */
/* /// let mut s = StringWrapper::new("all the king's men"); */
/* /// assert!(r.replace(&mut s, "duh")); */
/* /// assert_eq!(s.as_str(), "all duh king's men"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn replace(&self, s: &mut StringWrapper, rewrite: &str) -> bool { */
/* let rewrite = StringView::from_str(rewrite); */
/* unsafe { re2::RE2_Replace(s.as_mut(), &self.0, rewrite.into()) } */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// use re2::*; */
/* /// */
/* /// let r = RE2::new(".he")?; */
/* /// let mut s = StringWrapper::new( */
/* ///   "all the king's horses and all the king's men"); */
/* /// assert_eq!(2, r.global_replace(&mut s, "duh")); */
/* /// assert_eq!( */
/* ///   s.as_str(), */
/* ///   "all duh king's horses and all duh king's men", */
/* /// ); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn global_replace(&self, s: &mut StringWrapper, rewrite: &str) ->
 * usize { */
/* let rewrite = StringView::from_str(rewrite); */
/* (unsafe { re2::RE2_GlobalReplace(s.as_mut(), &self.0, rewrite.into()) })
 * as usize */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), re2::error::CompileError> { */
/* /// use re2::*; */
/* /// */
/* /// let r = RE2::new("(.h)e")?; */
/* /// let mut s = StringWrapper::new("aaa"); */
/* /// assert!(r.extract("all the king's men", r"\1a", &mut s)); */
/* /// // FIXME: BROKEN!!! */
/* /// // assert_eq!(s.as_str(), "tha"); */
/* /// # Ok(()) */
/* /// # } */
/* /// ``` */
/* pub fn extract(&self, text: &str, rewrite: &str, out: &mut StringWrapper)
 * -> bool { */
/* let text = StringView::from_str(text); */
/* let rewrite = StringView::from_str(rewrite); */
/* unsafe { re2::RE2_Extract(text.into(), &self.0, rewrite.into(),
 * out.as_mut()) } */
/* } */

/* ///``` */
/* /// let q = re2::RE2::quote_meta("1.5-1.8?"); */
/* /// assert_eq!(q.as_str(), r"1\.5\-1\.8\?"); */
/* /// ``` */
/* pub fn quote_meta(pattern: &str) -> StringWrapper { */
/* let pattern = StringView::from_str(pattern); */
/* let mut w = StringWrapper::blank(); */
/* *w.as_mut() = unsafe { re2::RE2_QuoteMeta(pattern.into()) }; */
/* w */
/* } */
/* } */

/* unsafe extern "C" fn parse_str(str_: *const c_char, n: usize, dest: *mut
 * c_void) -> bool { */
/* let s = str::from_utf8_unchecked(slice::from_raw_parts(mem::transmute(str_), n)); */
/* let dest = dest as usize as *mut &str; */
/* dest.write(s); */
/* true */
/* } */

/* impl fmt::Debug for RE2 { */
/* fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { */
/* write!( */
/* f, */
/* "RE2(pattern=<{}>, options={:?})", */
/* self.pattern(), */
/* self.options() */
/* ) */
/* } */
/* } */

/* impl cmp::PartialEq for RE2 { */
/* fn eq(&self, other: &Self) -> bool { */
/* self.pattern().eq(other.pattern()) && self.options().eq(&other.options()) */
/* } */
/* } */

/* impl cmp::Eq for RE2 {} */

/* impl hash::Hash for RE2 { */
/* fn hash<H>(&self, state: &mut H) */
/* where H: hash::Hasher { */
/* self.pattern().hash(state); */
/* self.options().hash(state); */
/* } */
/* } */

/* impl cmp::PartialOrd for RE2 { */
/* fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { */
/* let p = self.pattern().partial_cmp(other.pattern())?; */
/* if p != cmp::Ordering::Equal { */
/* return Some(p); */
/* } */
/* self.options().partial_cmp(&other.options()) */
/* } */
/* } */

/* impl cmp::Ord for RE2 { */
/* fn cmp(&self, other: &Self) -> cmp::Ordering { */
/* let p = self.pattern().cmp(other.pattern()); */
/* if p != cmp::Ordering::Equal { */
/* return p; */
/* } */
/* self.options().cmp(&other.options()) */
/* } */
/* } */

/* /\* FIXME: why does this SIGABRT??? *\/ */
/* /\* impl ops::Drop for RE2 { *\/ */
/* /\* fn drop(&mut self) { *\/ */
/* /\* unsafe { *\/ */
/* /\* self.0.destruct(); *\/ */
/* /\* } *\/ */
/* /\* } *\/ */
/* /\* } *\/ */

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

#[allow(unused, improper_ctypes)]
mod bindings;

pub mod error;
use error::{CompileError, RE2ErrorCode};

pub(crate) use bindings::root::{absl as rebound_absl, re2};

use abseil::StringView;

use std::{
  cmp,
  ffi::CStr,
  fmt, hash, mem,
  os::raw::{c_char, c_void},
  ptr, slice, str,
};

#[derive(
  Default,
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
pub enum CannedOptions {
  #[default]
  DefaultOptions = re2::RE2_CannedOptions_DefaultOptions,
  Latin1 = re2::RE2_CannedOptions_Latin1,
  POSIX = re2::RE2_CannedOptions_POSIX,
  Quiet = re2::RE2_CannedOptions_Quiet,
}

impl CannedOptions {
  #[inline]
  pub fn into_native(self) -> re2::RE2_CannedOptions { self.into() }
}

#[derive(
  Default,
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
  #[default]
  Utf8 = re2::RE2_Options_Encoding_EncodingUTF8,
  Latin1 = re2::RE2_Options_Encoding_EncodingLatin1,
}

impl Encoding {
  #[inline]
  pub fn into_native(self) -> re2::RE2_Options_Encoding { self.into() }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Options {
  pub max_mem: u32,
  pub encoding: Encoding,
  pub posix_syntax: bool,
  pub longest_match: bool,
  pub log_errors: bool,
  pub literal: bool,
  pub never_nl: bool,
  pub dot_nl: bool,
  pub never_capture: bool,
  pub case_sensitive: bool,
  pub perl_classes: bool,
  pub word_boundary: bool,
  pub one_line: bool,
}

impl Options {
  #[inline]
  pub fn into_native(self) -> re2::RE2_Options {
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
      perl_classes,
      word_boundary,
      one_line,
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
  #[inline]
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
      perl_classes: perl_classes_,
      word_boundary: word_boundary_,
      one_line: one_line_,
    }
  }
}

impl From<CannedOptions> for Options {
  fn from(x: CannedOptions) -> Self { unsafe { re2::RE2_Options::new(x.into_native()) }.into() }
}

impl Default for Options {
  fn default() -> Self {
    Self {
      max_mem: 8 << 20,
      encoding: Encoding::Utf8,
      posix_syntax: false,
      longest_match: false,
      log_errors: true,
      literal: false,
      never_nl: false,
      dot_nl: false,
      never_capture: false,
      case_sensitive: true,
      perl_classes: false,
      word_boundary: false,
      one_line: false,
    }
  }
}

/* NB: mem::transmute is currently needed (but always safe) because we
 * duplicate any native bindings across each crate. */
impl<'a> From<StringView<'a>> for rebound_absl::lts_20230125::string_view {
  fn from(x: StringView<'a>) -> Self { unsafe { mem::transmute(x.inner) } }
}

///```
/// # fn main() -> Result<(), re2::error::CompileError> {
/// use re2::{RE2, error::*};
///
/// let r = RE2::new(".he")?;
/// assert!(r.full_match("the"));
/// assert!(!r.partial_match("hello"));
/// assert!(r.partial_match("othello"));
/// assert!(r.partial_match("the"));
///
/// assert_eq!(
///   RE2::new("as(df").err().unwrap(),
///   CompileError {
///     message: "missing ): as(df".to_string(),
///     arg: "as(df".to_string(),
///     code: RE2ErrorCode::MissingParen,
///   },
/// );
/// # Ok(())
/// # }
/// ```
#[repr(transparent)]
pub struct RE2(pub re2::RE2);

impl RE2 {
  #[inline]
  fn parse_c_str<'a>(p: *const c_char) -> Result<Option<&'a str>, str::Utf8Error> {
    if p.is_null() {
      return Ok(None);
    }
    let c_str: &'a CStr = unsafe { CStr::from_ptr(p) };
    Ok(Some(c_str.to_str()?))
  }

  fn check_error_state(&self) -> Result<(), CompileError> {
    RE2ErrorCode::from_native(self.0.error_code_()).map_err(|code| {
      let message = Self::parse_c_str(unsafe { self.0.error_c() })
        .unwrap()
        .unwrap()
        .to_string();
      let arg = Self::parse_c_str(unsafe { self.0.error_arg_c() })
        .unwrap()
        .unwrap()
        .to_string();
      CompileError { message, arg, code }
    })
  }

  pub fn new(pattern: impl AsRef<str>) -> Result<Self, CompileError> {
    let pattern = StringView::from_str(pattern.as_ref());
    let ret = Self(unsafe { re2::RE2::new2(pattern.into()) });
    ret.check_error_state()?;
    Ok(ret)
  }

  pub fn new_with_options(
    pattern: impl AsRef<str>,
    options: Options,
  ) -> Result<Self, CompileError> {
    let pattern = StringView::from_str(pattern.as_ref());
    let ret = Self(unsafe { re2::RE2::new3(pattern.into(), &options.into_native()) });
    ret.check_error_state()?;
    Ok(ret)
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// use re2::*;
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let r = re2::RE2::new_with_options(".he", o)?;
  /// assert_eq!(o, r.options());
  /// assert_ne!(o, Options::default());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn options(&self) -> Options { self.0.options_.into() }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::new(".he")?;
  /// assert_eq!(".he", r.pattern());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn pattern(&self) -> &str {
    Self::parse_c_str(unsafe { self.0.pattern_c() })
      .unwrap()
      .unwrap()
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::new(".he")?;
  /// assert_eq!(0, r.num_captures());
  /// let r = re2::RE2::new("(.h)e")?;
  /// assert_eq!(1, r.num_captures());
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn num_captures(&self) -> usize { self.0.num_captures_ as usize }

  pub fn expensive_clone(&self) -> Self {
    Self::new_with_options(self.pattern(), self.options()).unwrap()
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::new(".he")?;
  /// assert!(r.full_match("the"));
  /// # Ok(())
  /// # }
  /// ```
  #[inline]
  pub fn full_match(&self, text: &str) -> bool {
    let text = StringView::from_str(text);
    unsafe { re2::RE2_FullMatchN(text.into(), &self.0, ptr::null(), 0) }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::new("(.h)e")?;
  /// assert_eq!(1, r.num_captures());
  /// let [s] = r.full_match_capturing("the").unwrap();
  /// assert_eq!(s, "th");
  /// # Ok(())
  /// # }
  /// ```
  pub fn full_match_capturing<'a, const N: usize>(&self, text: &'a str) -> Option<[&'a str; N]> {
    if N > self.num_captures() {
      return None;
    }
    let mut args: [mem::MaybeUninit<&'a str>; N] = mem::MaybeUninit::uninit_array();
    let argv: [re2::RE2_Arg; N] = {
      let mut argv: [mem::MaybeUninit<re2::RE2_Arg>; N] = mem::MaybeUninit::uninit_array();
      for (a, arg) in args.iter_mut().zip(argv.iter_mut()) {
        arg.write(re2::RE2_Arg {
          arg_: a.as_mut_ptr() as usize as *mut c_void,
          parser_: Some(parse_str),
        });
      }
      unsafe { mem::MaybeUninit::array_assume_init(argv) }
    };
    let argv_ref: [*const re2::RE2_Arg; N] = {
      let mut argv_ref: [mem::MaybeUninit<*const re2::RE2_Arg>; N] =
        mem::MaybeUninit::uninit_array();
      for (a, arg) in argv.iter().zip(argv_ref.iter_mut()) {
        arg.write(unsafe { mem::transmute(a) });
      }
      unsafe { mem::MaybeUninit::array_assume_init(argv_ref) }
    };
    if unsafe {
      re2::RE2_FullMatchN(
        StringView::from_str(text).into(),
        &self.0,
        argv_ref.as_ptr(),
        argv_ref.len() as i32,
      )
    } {
      Some(unsafe { mem::MaybeUninit::array_assume_init(args) })
    } else {
      None
    }
  }

  #[inline]
  pub fn partial_match(&self, text: &str) -> bool {
    let text = StringView::from_str(text);
    unsafe { re2::RE2_PartialMatchN(text.into(), &self.0, ptr::null(), 0) }
  }

  ///```
  /// # fn main() -> Result<(), re2::error::CompileError> {
  /// let r = re2::RE2::new("(.h)e")?;
  /// assert_eq!(1, r.num_captures());
  /// let [s] = r.partial_match_capturing("othello").unwrap();
  /// assert_eq!(s, "th");
  ///
  /// // Ensure it uses the same memory (no copying):
  /// let data = "this is the source string";
  /// let [s] = r.partial_match_capturing(data).unwrap();
  /// assert_eq!(s, "th");
  /// assert_eq!(s.as_bytes().as_ptr(), data[8..].as_bytes().as_ptr());
  /// # Ok(())
  /// # }
  /// ```
  pub fn partial_match_capturing<'a, const N: usize>(&self, text: &'a str) -> Option<[&'a str; N]> {
    if N > self.num_captures() {
      return None;
    }
    let mut args: [mem::MaybeUninit<&'a str>; N] = mem::MaybeUninit::uninit_array();
    let argv: [re2::RE2_Arg; N] = {
      let mut argv: [mem::MaybeUninit<re2::RE2_Arg>; N] = mem::MaybeUninit::uninit_array();
      for (a, arg) in args.iter_mut().zip(argv.iter_mut()) {
        arg.write(re2::RE2_Arg {
          arg_: a.as_mut_ptr() as usize as *mut c_void,
          parser_: Some(parse_str),
        });
      }
      unsafe { mem::MaybeUninit::array_assume_init(argv) }
    };
    let argv_ref: [*const re2::RE2_Arg; N] = {
      let mut argv_ref: [mem::MaybeUninit<*const re2::RE2_Arg>; N] =
        mem::MaybeUninit::uninit_array();
      for (a, arg) in argv.iter().zip(argv_ref.iter_mut()) {
        arg.write(unsafe { mem::transmute(a) });
      }
      unsafe { mem::MaybeUninit::array_assume_init(argv_ref) }
    };
    if unsafe {
      re2::RE2_PartialMatchN(
        StringView::from_str(text).into(),
        &self.0,
        argv_ref.as_ptr(),
        argv_ref.len() as i32,
      )
    } {
      Some(unsafe { mem::MaybeUninit::array_assume_init(args) })
    } else {
      None
    }
  }
}

unsafe extern "C" fn parse_str(str_: *const c_char, n: usize, dest: *mut c_void) -> bool {
  let s = str::from_utf8_unchecked(slice::from_raw_parts(mem::transmute(str_), n));
  let dest = dest as usize as *mut &str;
  dest.write(s);
  true
}

impl fmt::Debug for RE2 {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "RE2(pattern=<{}>, options={:?})",
      self.pattern(),
      self.options()
    )
  }
}

impl cmp::PartialEq for RE2 {
  fn eq(&self, other: &Self) -> bool {
    self.pattern().eq(other.pattern()) && self.options().eq(&other.options())
  }
}

impl cmp::Eq for RE2 {}

impl hash::Hash for RE2 {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.pattern().hash(state);
    self.options().hash(state);
  }
}

impl cmp::PartialOrd for RE2 {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
    let p = self.pattern().partial_cmp(other.pattern())?;
    if p != cmp::Ordering::Equal {
      return Some(p);
    }
    self.options().partial_cmp(&other.options())
  }
}

impl cmp::Ord for RE2 {
  fn cmp(&self, other: &Self) -> cmp::Ordering {
    let p = self.pattern().cmp(other.pattern());
    if p != cmp::Ordering::Equal {
      return p;
    }
    self.options().cmp(&other.options())
  }
}

/* FIXME: why does this SIGABRT??? */
/* impl ops::Drop for RE2 { */
/* fn drop(&mut self) { */
/* unsafe { */
/* self.0.destruct(); */
/* } */
/* } */
/* } */

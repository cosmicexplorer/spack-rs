/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use crate::{
  error::{SetCompileError, SetErrorInfo, SetPatternError},
  filtered::AtomIndex,
  options::{Anchor, Options},
  re2, re2_c,
  string::{StringView, StringWrapper},
};

use std::{
  mem::{self, ManuallyDrop, MaybeUninit},
  ops,
  os::raw::c_int,
  ptr, slice, str,
};

#[derive(Debug)]
#[repr(transparent)]
pub struct MatchedSetInfo(re2_c::MatchedSetInfo);

impl MatchedSetInfo {
  pub const fn empty() -> Self {
    Self(re2_c::MatchedSetInfo {
      matches_: ptr::null_mut(),
    })
  }

  pub(crate) fn as_ref_native(&self) -> &re2_c::MatchedSetInfo { &self.0 }

  pub(crate) fn as_mut_native(&mut self) -> &mut re2_c::MatchedSetInfo { &mut self.0 }

  pub fn as_expression_slice(&self) -> &[ExpressionIndex] {
    unsafe { slice::from_raw_parts(self.data_pointer(), self.len()) }
  }

  pub fn as_mut_expression_slice(&mut self) -> &mut [ExpressionIndex] {
    unsafe { slice::from_raw_parts_mut(mem::transmute(self.0.data()), self.len()) }
  }

  pub fn as_atom_slice(&self) -> &[AtomIndex] {
    unsafe { slice::from_raw_parts(self.atom_data_pointer(), self.len()) }
  }

  pub fn as_mut_atom_slice(&self) -> &mut [AtomIndex] {
    unsafe { slice::from_raw_parts_mut(mem::transmute(self.0.data()), self.len()) }
  }

  pub fn capacity(&self) -> usize { unsafe { self.0.capacity() } }

  pub fn reserve(&mut self, to: usize) {
    unsafe {
      self.0.reserve(to);
    }
  }

  pub fn set_len(&mut self, to: usize) {
    unsafe {
      self.0.set_len(to);
    }
  }

  pub fn len(&self) -> usize { unsafe { self.0.size() } }

  pub fn is_empty(&self) -> bool { self.len() == 0 }

  unsafe fn data_pointer(&self) -> *const ExpressionIndex { mem::transmute(self.0.data()) }

  unsafe fn atom_data_pointer(&self) -> *const AtomIndex { mem::transmute(self.0.data()) }
}

impl ops::Drop for MatchedSetInfo {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub(crate) c_int);

impl ExpressionIndex {
  pub const fn as_index(self) -> u16 { self.0 as u16 }

  pub const fn from_index(x: u16) -> Self { Self(x as c_int) }
}

impl From<ExpressionIndex> for u16 {
  fn from(x: ExpressionIndex) -> Self { x.as_index() }
}

#[repr(transparent)]
pub struct SetBuilder(re2_c::SetWrapper);

impl SetBuilder {
  pub fn new(options: Options, anchor: Anchor) -> Self {
    Self(unsafe { re2_c::SetWrapper::new(&options.into_native(), anchor.into_native()) })
  }

  pub fn add_view(&mut self, pattern: StringView) -> Result<ExpressionIndex, SetPatternError> {
    let mut error = StringWrapper::blank();
    let ret: c_int = unsafe { self.0.add(pattern.into_native(), error.as_mut_native()) };

    if ret == -1 {
      Err(SetPatternError {
        message: error.as_view().as_str().to_string(),
      })
    } else {
      assert!(ret <= u8::MAX as c_int);
      Ok(ExpressionIndex(ret))
    }
  }

  ///```
  /// use re2::{options::*, error::*, set::*};
  ///
  /// let mut b = SetBuilder::new(Options::default(), Anchor::Unanchored);
  /// assert_eq!(
  ///   SetPatternError { message: "missing ): as(df".to_string() },
  ///   b.add("as(df").err().unwrap(),
  /// );
  /// ```
  pub fn add(&mut self, pattern: &str) -> Result<ExpressionIndex, SetPatternError> {
    self.add_view(StringView::from_str(pattern))
  }

  pub fn compile(self) -> Result<Set, SetCompileError> {
    let mut s: ManuallyDrop<Self> = ManuallyDrop::new(self);
    if unsafe { s.0.compile() } {
      Ok(Set(re2_c::SetWrapper { set_: s.0.set_ }))
    } else {
      Err(SetCompileError::OutOfMemory)
    }
  }
}

impl ops::Drop for SetBuilder {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

///```
/// use re2::{set::*, options::*};
///
/// let mut b = SetBuilder::new(Options::default(), Anchor::Unanchored);
/// assert_eq!(0, b.add("a+").unwrap().as_index());
/// assert_eq!(1, b.add("b+").unwrap().as_index());
/// let _ = b.compile().unwrap();
/// ```
#[repr(transparent)]
pub struct Set(pub(crate) re2_c::SetWrapper);

impl Set {
  pub fn match_routine_view(&self, text: StringView, matches: &mut MatchedSetInfo) -> bool {
    unsafe {
      self
        .0
        .match_routine(text.into_native(), matches.as_mut_native())
    }
  }

  ///```
  /// use re2::{set::*, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let mut b = SetBuilder::new(o, Anchor::Unanchored);
  /// let e1 = b.add("a+").unwrap();
  /// let e2 = b.add("b+").unwrap();
  /// let s = b.compile().unwrap();
  ///
  /// let mut m = MatchedSetInfo::empty();
  /// // a+ pattern matched:
  /// assert!(s.match_routine("asdf", &mut m));
  /// assert_eq!(&[e1], m.as_expression_slice());
  /// // neither pattern matched:
  /// assert!(!s.match_routine("csdf", &mut m));
  /// assert!(m.as_expression_slice().is_empty());
  /// // b+ pattern matched:
  /// assert!(s.match_routine("bsdf", &mut m));
  /// assert_eq!(&[e2], m.as_expression_slice());
  /// ```
  pub fn match_routine(&self, text: &str, matches: &mut MatchedSetInfo) -> bool {
    self.match_routine_view(StringView::from_str(text), matches)
  }

  pub fn match_routine_with_error_view(
    &self,
    text: StringView,
    matches: &mut MatchedSetInfo,
  ) -> Result<bool, SetErrorInfo> {
    let mut error: MaybeUninit<re2::RE2_Set_ErrorInfo> = MaybeUninit::uninit();
    if unsafe {
      self.0.match_routine_with_error(
        text.into_native(),
        matches.as_mut_native(),
        error.as_mut_ptr(),
      )
    } {
      Ok(true)
    } else {
      SetErrorInfo::from_native(unsafe { error.assume_init() })?;
      Ok(false)
    }
  }

  ///```
  /// use re2::{set::*, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let mut b = SetBuilder::new(o, Anchor::Unanchored);
  /// let e1 = b.add("a+").unwrap();
  /// let e2 = b.add("b+").unwrap();
  /// let s = b.compile().unwrap();
  ///
  /// let mut m = MatchedSetInfo::empty();
  /// // a+ pattern matched:
  /// assert!(s.match_routine_with_error("asdf", &mut m).unwrap());
  /// assert_eq!(&[e1], m.as_expression_slice());
  /// // neither pattern matched:
  /// assert!(!s.match_routine_with_error("csdf", &mut m).unwrap());
  /// assert!(m.as_expression_slice().is_empty());
  /// // b+ pattern matched:
  /// assert!(s.match_routine_with_error("bsdf", &mut m).unwrap());
  /// assert_eq!(&[e2], m.as_expression_slice());
  /// ```
  pub fn match_routine_with_error(
    &self,
    text: &str,
    matches: &mut MatchedSetInfo,
  ) -> Result<bool, SetErrorInfo> {
    self.match_routine_with_error_view(StringView::from_str(text), matches)
  }
}

impl ops::Drop for Set {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

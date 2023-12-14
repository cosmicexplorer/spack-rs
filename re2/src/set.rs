/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Routines for matching against multiple separate patterns at once.

#[cfg(doc)]
use crate::filtered::{Filter, FilteredRE2};
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

/// Holds the result of matching against a set of patterns.
///
/// This object can be interpreted as containing a slice of [`ExpressionIndex`],
/// [`AtomIndex`], or even both; [`Filter`] works by
/// correlating expressions to atoms. In general though, this will be a slice of
/// expressions when used with [`Set`], and a slice of atoms when used with
/// [`FilteredRE2`]. It is a logic error but not `unsafe` to interpret an
/// [`AtomIndex`] as an [`ExpressionIndex`] and vice versa.
///
/// This object holds a reference to a dynamically-allocated C++
/// `std::vector<int>`, which can be reused across calls to avoid allocations.
#[derive(Debug)]
#[repr(transparent)]
pub struct MatchedSetInfo(re2_c::MatchedSetInfo);

impl MatchedSetInfo {
  /// Generate an instance without allocating any memory dynamically.
  ///
  ///```
  /// let s = re2::set::MatchedSetInfo::empty();
  /// assert!(s.as_expression_slice().is_empty());
  /// ```
  pub const fn empty() -> Self {
    Self(re2_c::MatchedSetInfo {
      matches_: ptr::null_mut(),
    })
  }

  pub(crate) fn as_ref_native(&self) -> &re2_c::MatchedSetInfo { &self.0 }

  pub(crate) fn as_mut_native(&mut self) -> &mut re2_c::MatchedSetInfo { &mut self.0 }

  /// Interpret this `std::vector<int>` as a slice of expression indices.
  pub fn as_expression_slice(&self) -> &[ExpressionIndex] {
    unsafe { slice::from_raw_parts(self.data_pointer(), self.len()) }
  }

  /// Interpret this `std::vector<int>` as a mutable slice of expression
  /// indices.
  pub fn as_mut_expression_slice(&mut self) -> &mut [ExpressionIndex] {
    unsafe { slice::from_raw_parts_mut(mem::transmute(self.0.data()), self.len()) }
  }

  /// Interpret this `std::vector<int>` as a slice of atom indices.
  pub fn as_atom_slice(&self) -> &[AtomIndex] {
    unsafe { slice::from_raw_parts(self.atom_data_pointer(), self.len()) }
  }

  /// Interpret this `std::vector<int>` as a mutable slice of atom indices.
  pub fn as_mut_atom_slice(&mut self) -> &mut [AtomIndex] {
    unsafe { slice::from_raw_parts_mut(mem::transmute(self.0.data()), self.len()) }
  }

  /// Return the capacity of the backing vector.
  pub fn capacity(&self) -> usize { unsafe { self.0.capacity() } }

  /// Ensure the backing vector has at least `to` contiguous elements.
  pub fn reserve(&mut self, to: usize) {
    unsafe {
      self.0.reserve(to);
    }
  }

  /// Set the number of readable elements to `to`.
  pub fn set_len(&mut self, to: usize) {
    unsafe {
      self.0.set_len(to);
    }
  }

  /// Get the number of matches.
  pub fn len(&self) -> usize { unsafe { self.0.size() } }

  /// Whether any matches were found.
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

/// Identifier for sub-patterns within a [`Set`].
///
/// Wrapper for [`c_int`]. Indices start at 0 and are returned by
/// [`SetBuilder::add`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(pub(crate) c_int);

impl ExpressionIndex {
  /// Interpret this [`c_int`] value as the largest possible unsigned integer
  /// type it can represent.
  #[allow(clippy::absurd_extreme_comparisons)]
  pub const fn as_index(self) -> u16 {
    static_assertions::const_assert!(u16::MAX as c_int <= c_int::MAX);
    self.0 as u16
  }

  /// Generate an index from an unsigned integer guaranteed to fit into a
  /// [`c_int`] without wrapping.
  pub const fn from_index(x: u16) -> Self { Self(x as c_int) }
}

/// Mutable builder interface to create a [`Set`].
#[repr(transparent)]
pub struct SetBuilder(re2_c::SetWrapper);

impl SetBuilder {
  /// Generate a new instance. The provided `options` and `anchor` will apply to
  /// every pattern in the built set.
  pub fn new(options: Options, anchor: Anchor) -> Self {
    Self(unsafe { re2_c::SetWrapper::new(&options.into_native(), anchor.into_native()) })
  }

  pub(crate) fn add_view(
    &mut self,
    pattern: StringView,
  ) -> Result<ExpressionIndex, SetPatternError> {
    let mut error = StringWrapper::blank();
    let ret: c_int = unsafe { self.0.add(pattern.into_native(), error.as_mut_native()) };

    if ret == -1 {
      Err(SetPatternError {
        message: String::from_utf8_lossy(error.as_view().as_slice()).to_string(),
      })
    } else {
      assert!(ret <= u8::MAX as c_int);
      Ok(ExpressionIndex(ret))
    }
  }

  /// Add `pattern` to the set using the options passed to the constructor.
  /// Returns the index that will identify the regexp in the output of
  /// [`Set::match_routine()`].
  ///
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

  /// Compiles the set in preparation for matching.
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

/// Multiple pattern compiler with restricted matching interface.
///
/// Created by [`SetBuilder::compile()`].
///
///```
/// # fn main() -> Result<(), re2::error::SetError> {
/// use re2::{set::*, options::*};
///
/// let mut builder = SetBuilder::new(Options::default(), Anchor::Unanchored);
/// let a = builder.add("a+")?;
/// let b = builder.add("b+")?;
/// let s = builder.compile()?;
///
/// let mut m = MatchedSetInfo::empty();
/// assert!(s.match_routine_with_error("aaaa bbbb", &mut m)?);
/// assert_eq!(m.as_expression_slice(), &[a, b]);
/// # Ok(())
/// # }
/// ```
#[repr(transparent)]
pub struct Set(pub(crate) re2_c::SetWrapper);

impl Set {
  pub(crate) fn match_routine_view(&self, text: StringView, matches: &mut MatchedSetInfo) -> bool {
    unsafe {
      self
        .0
        .match_routine(text.into_native(), matches.as_mut_native())
    }
  }

  /// Match all of this set's patterns against `text` and record the result in
  /// `matches`.
  ///
  /// `matches` will be cleared (but not reallocated) before being modified.
  /// Returns [`true`] if any pattern was matched (so the result should be
  /// non-empty), otherwise [`false`].
  ///
  /// Callers must not expect any particular sorting of `matches`.
  ///
  ///```
  /// # fn main() -> Result<(), re2::error::SetError> {
  /// use re2::{set::*, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let mut b = SetBuilder::new(o, Anchor::Unanchored);
  /// let e1 = b.add("a+")?;
  /// let e2 = b.add("b+")?;
  /// let s = b.compile()?;
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
  /// # Ok(())
  /// # }
  /// ```
  pub fn match_routine(&self, text: &str, matches: &mut MatchedSetInfo) -> bool {
    self.match_routine_view(StringView::from_str(text), matches)
  }

  pub(crate) fn match_routine_with_error_view(
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

  /// Like [`Self::match_routine()`], but reports a wider range of reasons for
  /// failure to match. This can inform callers when DFA execution fails, for
  /// example, because they might wish to handle that case differently.
  ///
  ///```
  /// # fn main() -> Result<(), re2::error::SetError> {
  /// use re2::{set::*, options::*};
  ///
  /// let o: Options = CannedOptions::POSIX.into();
  /// let mut b = SetBuilder::new(o, Anchor::Unanchored);
  /// let e1 = b.add("a+")?;
  /// let e2 = b.add("b+")?;
  /// let s = b.compile()?;
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
  /// # Ok(())
  /// # }
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

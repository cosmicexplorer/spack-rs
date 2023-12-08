/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  error::RE2ErrorCode,
  options::Options,
  re2_c,
  string::{StringView, StringWrapper},
};

use std::{mem, ops, os::raw::c_int, slice};


#[derive(Debug)]
#[repr(transparent)]
pub struct StringSet(re2_c::StringSet);

impl StringSet {
  #[inline]
  pub(crate) const fn from_native(s: re2_c::StringSet) -> Self { Self(s) }

  fn as_ptr(&mut self) -> *mut re2_c::StringWrapper { unsafe { self.0.data() } }

  fn len(&self) -> usize { unsafe { self.0.size() } }

  pub fn as_mut_slice(&mut self) -> &mut [StringWrapper] {
    unsafe { mem::transmute(slice::from_raw_parts_mut(self.as_ptr(), self.len())) }
  }
}

impl ops::Drop for StringSet {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PatternId(pub(crate) c_int);

impl PatternId {
  #[inline]
  pub const fn as_index(self) -> u8 { self.0 as u8 }

  #[inline]
  pub(crate) const fn from_native(x: c_int) -> Option<Self> {
    if x == -1 {
      None
    } else {
      Some(Self(x))
    }
  }
}

impl From<PatternId> for u8 {
  fn from(x: PatternId) -> Self { x.as_index() }
}

///```
/// # fn main() -> Result<(), re2::error::RE2Error> {
/// use re2::{filtered::*, options::*};
///
/// let mut builder = FilteredRE2Builder::new();
/// let x = builder.add("asdf", Options::default())?;
/// assert_eq!(0, x.as_index());
/// let y = builder.add("aaay", Options::default())?;
/// assert_eq!(1, y.as_index());
///
/// assert_eq!(Some(x), builder.slow_first_match("asdf"));
/// assert_eq!(Some(y), builder.slow_first_match("aaay"));
/// assert_eq!(None, builder.slow_first_match("bsdf"));
/// # Ok(())
/// # }
///```
#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredRE2Builder(re2_c::FilteredRE2Wrapper);

impl FilteredRE2Builder {
  pub fn new() -> Self { Self(unsafe { re2_c::FilteredRE2Wrapper::new() }) }

  pub fn add(
    &mut self,
    pattern: &str,
    options: Options,
  ) -> Result<PatternId, RE2ErrorCode> {
    let pattern = StringView::from_str(pattern);
    let mut id = mem::MaybeUninit::<c_int>::uninit();
    RE2ErrorCode::from_native(unsafe {
      self.0.add(
        pattern.into_native(),
        &options.into_native(),
        id.as_mut_ptr(),
      )
    })?;
    Ok(PatternId(unsafe { id.assume_init() }))
  }

  pub fn compile(self) -> (FilteredRE2, StringSet) {
    let mut s: mem::ManuallyDrop<Self> = mem::ManuallyDrop::new(self);
    let mut set = mem::MaybeUninit::<re2_c::StringSet>::uninit();
    unsafe {
      s.0.compile(set.as_mut_ptr());
    }
    let set = StringSet::from_native(unsafe { set.assume_init() });
    let ret = FilteredRE2::from_native(re2_c::FilteredRE2Wrapper { inner_: s.0.inner_ });
    (ret, set)
  }

  pub fn slow_first_match(&self, text: &str) -> Option<PatternId> {
    let text = StringView::from_str(text);
    let ret = unsafe { self.0.slow_first_match(text.into_native()) };
    PatternId::from_native(ret)
  }
}

impl ops::Drop for FilteredRE2Builder {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredRE2(re2_c::FilteredRE2Wrapper);

impl FilteredRE2 {
  #[inline]
  pub(crate) const fn from_native(w: re2_c::FilteredRE2Wrapper) -> Self { Self(w) }
}

impl ops::Drop for FilteredRE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

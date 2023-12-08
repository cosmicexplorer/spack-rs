/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  error::RE2ErrorCode,
  options::Options,
  re2_c,
  set::{ExpressionIndex, MatchedSetInfo},
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
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredRE2Builder(re2_c::FilteredRE2Wrapper);

impl FilteredRE2Builder {
  pub fn new() -> Self { Self(unsafe { re2_c::FilteredRE2Wrapper::new() }) }

  pub fn with_min_atom_length(min_atom_len: usize) -> Self {
    Self(unsafe { re2_c::FilteredRE2Wrapper::new1(min_atom_len as c_int) })
  }

  pub fn add(&mut self, pattern: &str, options: Options) -> Result<ExpressionIndex, RE2ErrorCode> {
    let pattern = StringView::from_str(pattern);
    let mut id = mem::MaybeUninit::<c_int>::uninit();
    RE2ErrorCode::from_native(unsafe {
      self.0.add(
        pattern.into_native(),
        &options.into_native(),
        id.as_mut_ptr(),
      )
    })?;
    Ok(ExpressionIndex(unsafe { id.assume_init() }))
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

  pub fn slow_first_match(&self, text: &str) -> Option<ExpressionIndex> {
    let text = StringView::from_str(text);
    let ret = unsafe { self.0.slow_first_match(text.into_native()) };
    if ret == -1 {
      None
    } else {
      Some(ExpressionIndex(ret))
    }
  }
}

impl ops::Drop for FilteredRE2Builder {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

///```
/// # fn main() -> Result<(), re2::error::RE2Error> {
/// use re2::{filtered::*, set::*, options::*};
///
/// let mut builder = FilteredRE2Builder::with_min_atom_length(1);
/// let x = builder.add("asdf", Options::default())?;
/// let y = builder.add("asay", Options::default())?;
/// let z = builder.add("as+", Options::default())?;
///
/// let (filter, mut strings) = builder.compile();
/// let strings: Vec<&str> = strings.as_mut_slice().iter().map(|s| s.as_view().as_str()).collect();
/// assert_eq!(&strings, &["s", "a", "asay", "asdf"]);
///
/// let mut atoms = MatchedSetInfo::empty();
/// atoms.set_len(3);
/// let s = atoms.as_mut_slice();
/// s[0] = x;
/// s[1] = y;
/// s[2] = z;
/// let m = filter.first_match("asdf asay asasas", &atoms).unwrap();
/// assert_eq!(m, y);
///
/// let mut matches = MatchedSetInfo::empty();
/// matches.reserve(3);
/// assert!(filter.all_matches("asdf asay asasas", &atoms, &mut matches));
/// assert_eq!(matches.as_slice(), &[y, z]);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredRE2(re2_c::FilteredRE2Wrapper);

impl FilteredRE2 {
  #[inline]
  pub(crate) const fn from_native(w: re2_c::FilteredRE2Wrapper) -> Self { Self(w) }

  pub fn first_match(&self, text: &str, atoms: &MatchedSetInfo) -> Option<ExpressionIndex> {
    let text = StringView::from_str(text);
    let ret = unsafe {
      self
        .0
        .first_match(text.into_native(), atoms.as_ref_native())
    };
    if ret == -1 {
      None
    } else {
      Some(ExpressionIndex(ret))
    }
  }

  pub fn all_matches(
    &self,
    text: &str,
    atoms: &MatchedSetInfo,
    matching_regexps: &mut MatchedSetInfo,
  ) -> bool {
    let text = StringView::from_str(text);
    unsafe {
      self.0.all_matches(
        text.into_native(),
        atoms.as_ref_native(),
        matching_regexps.as_mut_native(),
      )
    }
  }
}

impl ops::Drop for FilteredRE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

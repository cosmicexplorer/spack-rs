/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{
  error::RE2ErrorCode,
  options::Options,
  re2, re2_c,
  set::{ExpressionIndex, MatchedSetInfo},
  string::{StringView, StringWrapper},
  RE2,
};

use indexmap::IndexMap;

use std::{marker::PhantomData, mem, ops, os::raw::c_int, slice};


#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AtomIndex(pub(crate) c_int);

impl AtomIndex {
  #[inline]
  pub const fn as_index(self) -> u8 { self.0 as u8 }

  #[inline]
  pub const fn from_index(x: u8) -> Self { Self(x as c_int) }
}

impl From<AtomIndex> for u8 {
  fn from(x: AtomIndex) -> Self { x.as_index() }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct AtomSet(re2_c::StringSet);

impl AtomSet {
  #[inline]
  pub(crate) const fn from_native(s: re2_c::StringSet) -> Self { Self(s) }

  fn as_ptr(&self) -> *const re2_c::StringWrapper { unsafe { self.0.cdata() } }

  fn as_mut_ptr(&mut self) -> *mut re2_c::StringWrapper { unsafe { self.0.data() } }

  fn len(&self) -> usize { unsafe { self.0.size() } }

  pub fn as_slice(&self) -> &[StringWrapper] {
    unsafe { mem::transmute(slice::from_raw_parts(self.as_ptr(), self.len())) }
  }

  pub fn as_mut_slice(&mut self) -> &mut [StringWrapper] {
    unsafe { mem::transmute(slice::from_raw_parts_mut(self.as_mut_ptr(), self.len())) }
  }

  pub fn indexed_atoms(&self) -> impl Iterator<Item=(AtomIndex, &str)>+'_ {
    self
      .as_slice()
      .iter()
      .enumerate()
      .map(|(i, sw)| (AtomIndex(i as c_int), sw.as_view().as_str()))
  }
}

impl ops::Drop for AtomSet {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct SelectedAtoms<'a>(pub IndexMap<&'a str, AtomIndex>);

impl<'a> SelectedAtoms<'a> {
  pub fn from_atom_set(atom_set: &'a AtomSet) -> Self {
    Self(atom_set.indexed_atoms().map(|(x, y)| (y, x)).collect())
  }

  pub fn allocate_match_set(&self) -> MatchedSetInfo {
    let mut ret = MatchedSetInfo::empty();
    self.allocate_into_match_set(&mut ret);
    ret
  }

  pub fn allocate_into_match_set(&self, ret: &mut MatchedSetInfo) {
    ret.set_len(self.0.len());
    for (out_index, arg_index) in ret.as_mut_atom_slice().iter_mut().zip(self.0.values()) {
      *out_index = *arg_index;
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
  #[inline]
  pub fn new() -> Self { Self(unsafe { re2_c::FilteredRE2Wrapper::new() }) }

  #[inline]
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

  pub fn compile(self) -> (FilteredRE2, AtomSet) {
    let mut s: mem::ManuallyDrop<Self> = mem::ManuallyDrop::new(self);
    let mut set = mem::MaybeUninit::<re2_c::StringSet>::uninit();
    unsafe {
      s.0.compile(set.as_mut_ptr());
    }
    let set = AtomSet::from_native(unsafe { set.assume_init() });
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

  #[inline]
  pub fn num_regexps(&self) -> usize { unsafe { self.0.num_regexps() } }
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
pub struct InnerRE2<'o> {
  inner: mem::ManuallyDrop<RE2>,
  _ph: PhantomData<&'o u8>,
}

impl<'o> InnerRE2<'o> {
  pub(crate) fn new(inner: RE2) -> Self {
    Self {
      inner: mem::ManuallyDrop::new(inner),
      _ph: PhantomData,
    }
  }

  pub fn as_re2_ref(&self) -> &'o RE2 { unsafe { mem::transmute(&self.inner) } }
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
/// let (filter, atom_set) = builder.compile();
/// let patterns: Vec<_> = filter.inner_regexps()
///   .into_iter()
///   .map(|r| r.as_re2_ref().pattern().as_str())
///   .collect();
/// assert_eq!(&patterns, &["asdf", "asay", "as+"]);
///
/// let mut selected_atoms = SelectedAtoms::from_atom_set(&atom_set);
/// // These indices correspond to the strings generated by the .compile() command:
/// let atom_indices: Vec<(&str, AtomIndex)> =
///   selected_atoms.0.iter().map(|(x, y)| (*x, *y)).collect();
/// assert_eq!(4, atom_indices.len());
/// let s = *selected_atoms.0.get("s").unwrap();
/// let a = *selected_atoms.0.get("a").unwrap();
/// let asay = *selected_atoms.0.get("asay").unwrap();
/// let asdf = *selected_atoms.0.get("asdf").unwrap();
/// assert_eq!(&atom_indices, &[("s", s), ("a", a), ("asay", asay), ("asdf", asdf)]);
///
/// let mut atoms = selected_atoms.allocate_match_set();
///
/// // The results of .first_match() and .all_matches() correspond to the indices of the original
/// // regex patterns provided to the builder.
/// let m = filter.first_match("asdf asay asasas", &atoms).unwrap();
/// assert_eq!(m, x);
///
/// let mut matches = MatchedSetInfo::empty();
/// matches.reserve(3);
/// assert!(filter.all_matches("asdf asay asasas", &atoms, &mut matches));
/// assert_eq!(matches.as_expression_slice(), &[x, y, z]);
///
/// // Remove the "asdf" atom by directly editing the MatchedSetInfo object:
/// atoms.set_len(3);
/// // The `x` pattern will no longer be matched without the "asdf" atom activated:
/// assert!(filter.all_matches("asdf asay asasas", &atoms, &mut matches));
/// assert_eq!(matches.as_expression_slice(), &[y, z]);
///
/// // Remove the "asdf" atom, but this time by modifying the higher-level SelectedAtoms object:
/// assert!(selected_atoms.0.remove("asdf").is_some());
/// selected_atoms.allocate_into_match_set(&mut atoms);
/// // We get the same results as before:
/// assert!(filter.all_matches("asdf asay asasas", &atoms, &mut matches));
/// assert_eq!(matches.as_expression_slice(), &[y, z]);
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

  #[inline]
  pub fn num_regexps(&self) -> usize { unsafe { self.0.num_regexps() } }

  #[inline]
  fn get_re2<'o>(&'o self, index: usize) -> InnerRE2<'o> {
    let re2_ptr: *const re2::RE2 = unsafe { self.0.get_re2(index as c_int) };
    InnerRE2::new(RE2(re2_c::RE2Wrapper {
      re_: unsafe { mem::transmute(re2_ptr) },
    }))
  }

  pub fn inner_regexps<'o>(&'o self) -> Vec<InnerRE2<'o>> {
    (0..self.num_regexps()).map(|i| self.get_re2(i)).collect()
  }
}

impl ops::Drop for FilteredRE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

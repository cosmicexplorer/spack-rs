/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Routines for extracting fixed string "atoms" from a set of patterns and
//! using those to pre-filter for later matching.

use crate::{
  error::{RE2ErrorCode, SetError},
  options::{Anchor, Options},
  re2, re2_c,
  set::{ExpressionIndex, MatchedSetInfo, Set, SetBuilder},
  string::{StringView, StringWrapper},
  RE2,
};

use indexmap::IndexMap;

use std::{marker::PhantomData, mem, ops, os::raw::c_int, slice};

/// Identifier for sub-patterns within an [`AtomSet`].
///
/// Wrapper for [`c_int`]. Indices start at 0 and are returned by
/// [`SetBuilder::add`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AtomIndex(pub(crate) c_int);

impl AtomIndex {
  /// Interpret this [`c_int`] value as the largest possible unsigned integer
  /// type it can represent.
  pub const fn as_index(self) -> u16 { self.0 as u16 }

  /// Generate an index from an unsigned integer guaranteed to fit into a
  /// [`c_int`] without wrapping.
  pub const fn from_index(x: u16) -> Self { Self(x as c_int) }
}

/// Holds the "atom" strings as a result of compiling a [`FilteredRE2Builder`].
///
/// This object owns a vector of [`StringWrapper`] instances and manages their
/// lifetime. It also serves as the canonical reference for [`AtomIndex`]
/// identifiers via [`Self::indexed_atoms()`] for traversal and
/// [`Self::index_by()`] for lookup.
#[derive(Debug)]
#[repr(transparent)]
pub struct AtomSet(re2_c::StringSet);

impl AtomSet {
  pub(crate) const fn from_native(s: re2_c::StringSet) -> Self { Self(s) }

  fn as_ptr(&self) -> *const re2_c::StringWrapper { unsafe { self.0.cdata() } }

  /// Return the number of atom strings.
  pub fn len(&self) -> usize { unsafe { self.0.size() } }

  /// Whether any atoms were extracted.
  pub fn is_empty(&self) -> bool { self.len() == 0 }

  /// Generate a Rust-compatible slice of read-only string handles.
  pub fn as_slice(&self) -> &[StringWrapper] {
    unsafe { mem::transmute(slice::from_raw_parts(self.as_ptr(), self.len())) }
  }

  /// Associate each atom with an [`AtomIndex`].
  pub fn indexed_atoms(
    &self,
  ) -> impl Iterator<Item=(AtomIndex, StringView<'_>)>+ExactSizeIterator+'_ {
    self
      .as_slice()
      .iter()
      .enumerate()
      .map(|(i, sw)| (AtomIndex(i as c_int), sw.as_view()))
  }

  /// Look up the registered atoms corresponding to the matches in `m`.
  pub fn index_by<'a>(
    &'a self,
    m: &'a MatchedSetInfo,
  ) -> impl Iterator<Item=&'a StringWrapper>+ExactSizeIterator+'a {
    let s = self.as_slice();
    m.as_atom_slice()
      .iter()
      .map(move |i| &s[i.as_index() as usize])
  }
}

impl ops::Drop for AtomSet {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

/// Higher-level Rust interface for selecting atoms to convert into a
/// [`MatchedSetInfo`] instance.
///
/// Modifications to the internal [`IndexMap`] instance will be reflected in the
/// output of [`Self::allocate_match_set()`] and
/// [`Self::allocate_into_match_set()`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct SelectedAtoms<'a>(pub IndexMap<StringView<'a>, AtomIndex>);

impl<'a> SelectedAtoms<'a> {
  /// Extract and index the known atoms.
  pub fn from_atom_set(atom_set: &'a AtomSet) -> Self {
    Self(atom_set.indexed_atoms().map(|(x, y)| (y, x)).collect())
  }

  /// Create and return new match set for the result of
  /// [`Self::allocate_into_match_set()`].
  pub fn allocate_match_set(&self) -> MatchedSetInfo {
    let mut ret = MatchedSetInfo::empty();
    self.allocate_into_match_set(&mut ret);
    ret
  }

  /// Modify `ret` to contain exactly the values from the internal [`IndexMap`].
  pub fn allocate_into_match_set(&self, ret: &mut MatchedSetInfo) {
    ret.set_len(self.0.len());
    for (out_index, arg_index) in ret.as_mut_atom_slice().iter_mut().zip(self.0.values()) {
      *out_index = *arg_index;
    }
  }
}

/// Mutable builder interface to create a [`FilteredRE2`].
///
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
  /// Generate a new instance with an arbitrary atom length.
  pub fn new() -> Self { Self(unsafe { re2_c::FilteredRE2Wrapper::new() }) }

  /// Generate a new instance with the specified minimum length for returned
  /// "atom" strings.
  pub fn with_min_atom_length(min_atom_len: usize) -> Self {
    Self(unsafe { re2_c::FilteredRE2Wrapper::new1(min_atom_len as c_int) })
  }

  /// [`Self::add()`] for arbitrary string encodings.
  pub fn add_view(
    &mut self,
    pattern: StringView,
    options: Options,
  ) -> Result<ExpressionIndex, RE2ErrorCode> {
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

  /// Use [`RE2::compile()`] to create an [`RE2`] object. The return value can
  /// be used in [`FilteredRE2::all_matches()`].
  pub fn add(&mut self, pattern: &str, options: Options) -> Result<ExpressionIndex, RE2ErrorCode> {
    self.add_view(StringView::from_str(pattern), options)
  }

  /// Prepares the regexps added by [`Self::add()`] for filtering. Returns a set
  /// of strings that the caller should check for in candidate texts
  /// ("atoms").
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

  /// [`Self::slow_first_match()`] for arbitrary string encodings.
  pub fn slow_first_match_view(&self, text: StringView) -> Option<ExpressionIndex> {
    let ret = unsafe { self.0.slow_first_match(text.into_native()) };
    if ret == -1 {
      None
    } else {
      Some(ExpressionIndex(ret))
    }
  }

  /// Returns the index of the first matching regexp.
  ///
  /// Does not do any filtering: simply tries to match the regexps in a loop.
  pub fn slow_first_match(&self, text: &str) -> Option<ExpressionIndex> {
    self.slow_first_match_view(StringView::from_str(text))
  }

  /// The number of regexps added.
  pub fn num_regexps(&self) -> usize { unsafe { self.0.num_regexps() } }
}

impl ops::Drop for FilteredRE2Builder {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

/// A reference to an [`RE2`] instance held somewhere else.
///
/// In particular, this is used to reference the regexps provided to
/// [`FilteredRE2Builder::add()`].
#[derive(Debug)]
#[repr(transparent)]
pub struct InnerRE2<'o> {
  inner: mem::ManuallyDrop<RE2>,
  _ph: PhantomData<&'o u8>,
}

impl<'o> InnerRE2<'o> {
  pub(crate) fn new(re2_ptr: *const re2::RE2) -> Self {
    let inner = RE2(re2_c::RE2Wrapper {
      re_: unsafe { mem::transmute(re2_ptr) },
    });
    Self {
      inner: mem::ManuallyDrop::new(inner),
      _ph: PhantomData,
    }
  }

  /// Extract the pattern reference.
  pub const fn as_re2(&self) -> &'o RE2 { unsafe { mem::transmute(&self.inner) } }
}

/// This struct is used as a wrapper to multiple [`RE2`] regexps.
/// It provides a prefilter mechanism that helps in cutting down the
/// number of regexps that need to be actually searched.
///
/// By design, it does not include a string matching engine. This is to
/// allow the user of the struct to use their favorite string matching
/// engine. The overall flow is:
/// - Add all the regexps using [`FilteredRE2Builder::add()`],
/// - then [`FilteredRE2Builder::compile()`].
///
/// `compile()` returns strings that need to be matched ("atoms" in an
/// [`AtomSet`]). Note that the returned strings are lowercased and distinct.
///
/// For applying regexps to a search text, the caller does the string
/// matching using the returned strings. When doing the string match,
/// note that the caller has to do that in a case-insensitive way or
/// on a lowercased version of the search text. Then call
/// [`Self::first_match()`] or [`Self::all_matches()`] with a vector of indices
/// of strings that were found in the text to get the actual regexp matches.
///
///```
/// # fn main() -> Result<(), re2::error::RE2Error> {
/// use re2::{filtered::*, set::*, options::*, string::*};
/// use indexmap::IndexMap;
///
/// let mut builder = FilteredRE2Builder::with_min_atom_length(1);
/// let x = builder.add("asdf", Options::default())?;
/// let y = builder.add("asay", Options::default())?;
/// let z = builder.add("as+", Options::default())?;
///
/// let (filter, atom_set) = builder.compile();
/// let patterns: Vec<_> = filter.inner_regexps()
///   .map(|r| unsafe { r.as_re2().pattern().as_str() })
///   .collect();
/// assert_eq!(&patterns, &["asdf", "asay", "as+"]);
///
/// let mut selected_atoms = SelectedAtoms::from_atom_set(&atom_set);
/// // These indices correspond to the strings generated by the .compile() command:
/// let atom_indices: IndexMap<&str, AtomIndex> = selected_atoms.0.iter()
///   .map(|(x, y)| (unsafe { x.as_str() }, *y))
///   .collect();
/// assert_eq!(4, atom_indices.len());
/// dbg!(&selected_atoms);
/// let s = *atom_indices.get("s").unwrap();
/// let a = *atom_indices.get("a").unwrap();
/// let asay = *atom_indices.get("asay").unwrap();
/// let asdf = *atom_indices.get("asdf").unwrap();
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
/// assert!(selected_atoms.0.remove(&StringView::from_str("asdf")).is_some());
/// selected_atoms.allocate_into_match_set(&mut atoms);
/// // We get the same results as before:
/// assert!(filter.all_matches("asdf asay asasas", &atoms, &mut matches));
/// assert_eq!(matches.as_expression_slice(), &[y, z]);
///
/// // Similarly, we can see that the "asay" atom matches the corresponding regexp:
/// let mut atoms = MatchedSetInfo::empty();
/// atoms.set_len(1);
/// atoms.as_mut_atom_slice()[0] = asay;
/// filter.all_potentials(&atoms, &mut matches);
/// assert_eq!(matches.as_expression_slice(), &[y]);
///
/// // If we expand the search to all atoms, we find all regexps as potential candidates:
/// atoms.set_len(4);
/// let ats = atoms.as_mut_atom_slice();
/// ats[1] = a;
/// ats[2] = s;
/// ats[3] = asdf;
/// filter.all_potentials(&atoms, &mut matches);
/// assert_eq!(matches.as_expression_slice(), &[x, y, z]);
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct FilteredRE2(re2_c::FilteredRE2Wrapper);

impl FilteredRE2 {
  pub(crate) const fn from_native(w: re2_c::FilteredRE2Wrapper) -> Self { Self(w) }

  /// [`Self::first_match()`] for arbitrary string encodings.
  pub fn first_match_view(
    &self,
    text: StringView,
    atoms: &MatchedSetInfo,
  ) -> Option<ExpressionIndex> {
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

  /// Return a pattern which contributed to one of the given `atoms` that
  /// matches `text`.
  pub fn first_match(&self, text: &str, atoms: &MatchedSetInfo) -> Option<ExpressionIndex> {
    self.first_match_view(StringView::from_str(text), atoms)
  }

  /// [`Self::all_matches()`] for arbitrary string encodings.
  pub fn all_matches_view(
    &self,
    text: StringView,
    atoms: &MatchedSetInfo,
    matching_regexps: &mut MatchedSetInfo,
  ) -> bool {
    unsafe {
      self.0.all_matches(
        text.into_native(),
        atoms.as_ref_native(),
        matching_regexps.as_mut_native(),
      )
    }
  }

  /// Return all patterns which contributed to any of the given `atoms` which
  /// match `text`.
  pub fn all_matches(
    &self,
    text: &str,
    atoms: &MatchedSetInfo,
    matching_regexps: &mut MatchedSetInfo,
  ) -> bool {
    self.all_matches_view(StringView::from_str(text), atoms, matching_regexps)
  }

  /// Return all patterns which contributed to any of the given `atoms`.
  pub fn all_potentials(
    &self,
    atoms: &MatchedSetInfo,
    potential_regexps: &mut MatchedSetInfo,
  ) -> bool {
    unsafe {
      self
        .0
        .all_potentials(atoms.as_ref_native(), potential_regexps.as_mut_native());
    }
    !potential_regexps.is_empty()
  }

  /// The number of regexps added.
  pub fn num_regexps(&self) -> usize { unsafe { self.0.num_regexps() } }

  fn get_re2<'o>(&'o self, index: usize) -> InnerRE2<'o> {
    let re2_ptr: *const re2::RE2 = unsafe { self.0.get_re2(index as c_int) };
    InnerRE2::new(re2_ptr)
  }

  /// Get references to the individual [`RE2`] objects.
  pub fn inner_regexps<'o>(&'o self) -> impl Iterator<Item=InnerRE2<'o>>+ExactSizeIterator {
    (0..self.num_regexps()).map(|i| self.get_re2(i))
  }

  /// Look up the constituent [`RE2`] objects according to the indices in `m`.
  pub fn index_by<'o>(
    &'o self,
    m: &'o MatchedSetInfo,
  ) -> impl Iterator<Item=InnerRE2<'o>>+ExactSizeIterator {
    let n = self.num_regexps();
    m.as_expression_slice().iter().map(move |i| {
      let i = i.as_index() as usize;
      assert!(i < n);
      self.get_re2(i)
    })
  }
}

impl ops::Drop for FilteredRE2 {
  fn drop(&mut self) {
    unsafe {
      self.0.clear();
    }
  }
}

/// [`Filter`] demonstrates the use of [`FilteredRE2`] by using
/// [`Set`] as the backing search engine for the atoms produced by `compile()`.
///
///```
/// # fn main() -> Result<(), re2::error::RE2Error> {
/// use re2::{filtered::*, options::*, set::*};
///
/// let mut builder = FilteredRE2Builder::with_min_atom_length(1);
/// let x = builder.add("asdf", Options::default())?;
/// let y = builder.add("asay", Options::default())?;
/// let z = builder.add("as+", Options::default())?;
/// let filter = Filter::compile(builder)?;
///
/// let mut atoms = MatchedSetInfo::empty();
/// let mut matches = MatchedSetInfo::empty();
/// assert!(filter.all_matches("asdf asay asinine", &mut atoms, &mut matches));
/// assert_eq!(matches.as_expression_slice(), &[x, y, z]);
///
/// let matched_atoms: Vec<&str> = filter.get_atoms(&atoms)
///   .map(|s| unsafe { s.as_str() })
///   .collect();
/// assert_eq!(&matched_atoms, &["a", "s", "asdf", "asay"]);
/// let matched_regexps: Vec<&str> = filter.get_matches(&matches)
///   .map(|r| unsafe { r.as_re2().pattern().as_str() })
///   .collect();
/// assert_eq!(&matched_regexps, &["asdf", "asay", "as+"]);
///
/// assert!(filter.potential_matches("asdf asay asinine", &mut atoms, &mut matches));
/// assert_eq!(matches.as_expression_slice(), &[x, y, z]);
/// # Ok(())
/// # }
/// ```
pub struct Filter {
  filter: FilteredRE2,
  atom_set: AtomSet,
  set: Set,
}

impl Filter {
  /// Extract the [`AtomSet`] from compiling the `builder`, then use it to
  /// construct a [`Set`] to search the atoms as literal case-insensitive
  /// strings.
  pub fn compile(builder: FilteredRE2Builder) -> Result<Self, SetError> {
    let (filter, atom_set) = builder.compile();

    let mut options = Options::default();
    options.literal = true;
    options.case_sensitive = false;
    let mut set_builder = SetBuilder::new(options, Anchor::Unanchored);
    for (i, atom) in atom_set.indexed_atoms() {
      let j = set_builder.add_view(atom)?;
      /* Ensure our atom indices are aligned with the set match indices so we can
       * convert a MatchedSetInfo from one into the other: */
      assert_eq!(i.as_index(), j.as_index());
    }

    let set = set_builder.compile()?;

    Ok(Self {
      filter,
      atom_set,
      set,
    })
  }

  /// [`Self::all_matches()`] for arbitrary string encodings.
  pub fn all_matches_view(
    &self,
    text: StringView,
    atoms: &mut MatchedSetInfo,
    matches: &mut MatchedSetInfo,
  ) -> bool {
    self.set.match_routine_view(text, atoms) && self.filter.all_matches_view(text, atoms, matches)
  }

  /// Get all patterns matching `text` contributing to `atoms` in `matches`.
  pub fn all_matches(
    &self,
    text: &str,
    atoms: &mut MatchedSetInfo,
    matches: &mut MatchedSetInfo,
  ) -> bool {
    self.all_matches_view(StringView::from_str(text), atoms, matches)
  }

  /// [`Self::potential_matches()`] for arbitrary string encodings.
  pub fn potential_matches_view(
    &self,
    text: StringView,
    atoms: &mut MatchedSetInfo,
    matches: &mut MatchedSetInfo,
  ) -> bool {
    self.set.match_routine_view(text, atoms) && self.filter.all_potentials(atoms, matches)
  }

  /// Get all patterns contributing to the `atoms` which were found in `text`
  /// into `matches`.
  pub fn potential_matches(
    &self,
    text: &str,
    atoms: &mut MatchedSetInfo,
    matches: &mut MatchedSetInfo,
  ) -> bool {
    self.potential_matches_view(StringView::from_str(text), atoms, matches)
  }

  /// Look up the atom strings referenced in `atoms`.
  pub fn get_atoms<'a>(
    &'a self,
    atoms: &'a MatchedSetInfo,
  ) -> impl Iterator<Item=StringView<'a>>+ExactSizeIterator {
    self.atom_set.index_by(atoms).map(|sw| sw.as_view())
  }

  /// Look up the pattern objects referenced in `matches`.
  pub fn get_matches<'a>(
    &'a self,
    matches: &'a MatchedSetInfo,
  ) -> impl Iterator<Item=InnerRE2<'a>>+ExactSizeIterator {
    self.filter.index_by(matches)
  }
}

/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{re2_c, string::StringView};

use std::{
  fmt,
  marker::PhantomData,
  mem::{self, MaybeUninit},
  str,
};

#[derive(Copy, Clone)]
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
pub(crate) struct NamedCapturingGroups<'a> {
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

pub(crate) struct NamedAndNumberedGroups<'a> {
  at_start: bool,
  total_num_captures: usize,
  groups_iter: Option<NamedCapturingGroups<'a>>,
  next_named_group: Option<NamedGroup<'a>>,
  cur_index: usize,
}

impl<'a> NamedAndNumberedGroups<'a> {
  pub fn new(total_num_captures: usize, groups_iter: NamedCapturingGroups<'a>) -> Self {
    Self {
      at_start: true,
      total_num_captures,
      groups_iter: Some(groups_iter),
      next_named_group: None,
      cur_index: 0,
    }
  }

  const fn remaining(&self) -> usize {
    if self.at_start {
      self.total_num_captures + 1
    } else {
      self.total_num_captures - self.cur_index + 1
    }
  }
}

impl<'a> Iterator for NamedAndNumberedGroups<'a> {
  type Item = Option<&'a str>;

  fn next(&mut self) -> Option<Self::Item> {
    let Self {
      ref mut at_start,
      ref total_num_captures,
      ref mut groups_iter,
      ref mut next_named_group,
      ref mut cur_index,
    } = self;

    /* Return 0th submatch (for whole pattern). */
    if *at_start {
      *at_start = false;
      *cur_index = 1;
      return Some(None);
    }

    if *cur_index > *total_num_captures {
      return None;
    }

    if next_named_group.is_none() {
      let reset_groups_iter = if let Some(ref mut g) = groups_iter {
        if g.completed() {
          true
        } else {
          *next_named_group = Some(g.deref());
          g.advance();
          false
        }
      } else {
        false
      };
      if reset_groups_iter {
        *groups_iter = None;
      }
    }
    let ret = if let Some(named_group) = next_named_group {
      if *cur_index < *named_group.index() {
        None
      } else {
        debug_assert_eq!(cur_index, named_group.index());
        Some(named_group.name().as_str())
      }
    } else {
      None
    };
    if ret.is_some() {
      *next_named_group = None;
    }

    *cur_index += 1;

    Some(ret)
  }

  fn size_hint(&self) -> (usize, Option<usize>) { (self.remaining(), Some(self.remaining())) }
}

impl<'a> ExactSizeIterator for NamedAndNumberedGroups<'a> {}

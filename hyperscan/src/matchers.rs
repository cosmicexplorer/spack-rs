/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use super::{ByteSlice, ExpressionIndex, MatchEvent, MatchResult, ScanFlags, VectoredByteSlices};

use parking_lot::Mutex;

use std::{
  cmp,
  collections::VecDeque,
  future::Future,
  ops,
  os::raw::{c_char, c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  task::{Context, Poll, Waker},
};

pub mod contiguous_slice {
  use super::*;

  #[derive(Debug)]
  pub struct Match<'a> {
    pub id: ExpressionIndex,
    pub source: ByteSlice<'a>,
    pub flags: ScanFlags,
  }

  pub trait Scanner<'data> = FnMut(&Match<'data>) -> MatchResult+'data;

  pub(crate) struct SliceMatcher<'data, 'code> {
    parent_slice: ByteSlice<'data>,
    matched_slices_queue: Mutex<VecDeque<Match<'data>>>,
    handler: &'code mut dyn Scanner<'data>,
    wakers: Mutex<Vec<Waker>>,
  }

  impl<'data, 'code> SliceMatcher<'data, 'code> {
    #[inline]
    pub fn new<F: Scanner<'data>>(parent_slice: ByteSlice<'data>, f: &'code mut F) -> Self {
      Self {
        parent_slice,
        matched_slices_queue: Mutex::new(VecDeque::new()),
        handler: f,
        wakers: Mutex::new(Vec::new()),
      }
    }

    #[inline(always)]
    const fn parent(&self) -> ByteSlice<'data> { self.parent_slice }

    #[inline(always)]
    pub fn pop(&mut self) -> Option<Match<'data>> { self.matched_slices_queue.lock().pop_front() }

    pub fn pop_rest(&mut self) -> Vec<Match<'data>> {
      self.matched_slices_queue.lock().drain(..).collect()
    }

    #[inline(always)]
    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      &self.parent()[range]
    }

    #[inline(always)]
    pub fn push_new_match(&mut self, m: Match<'data>) {
      self.matched_slices_queue.lock().push_back(m);
      for waker in self.wakers.lock().drain(..) {
        waker.wake();
      }
    }

    #[inline(always)]
    pub fn handle_match(&mut self, m: &Match<'data>) -> MatchResult { (self.handler)(m) }

    #[inline(always)]
    pub fn push_waker(&mut self, w: Waker) { self.wakers.lock().push(w); }
  }

  impl<'data, 'code> Future for SliceMatcher<'data, 'code> {
    type Output = Match<'data>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
      if let Some(m) = self.pop() {
        Poll::Ready(m)
      } else {
        self.push_waker(cx.waker().clone());
        Poll::Pending
      }
    }
  }

  pub(crate) unsafe extern "C" fn match_slice_ref(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    let MatchEvent {
      id,
      range,
      flags,
      context,
    } = MatchEvent::coerce_args(id, from, to, flags, context);
    let mut slice_matcher: Pin<&mut SliceMatcher> =
      MatchEvent::extract_context::<'_, SliceMatcher>(context).unwrap();
    let matched_substring = slice_matcher.index_range(range);
    let m = Match {
      id,
      source: matched_substring,
      flags,
    };

    let result = slice_matcher.handle_match(&m);
    if result == MatchResult::Continue {
      slice_matcher.push_new_match(m);
    }

    result.into_native()
  }

  #[cfg(test)]
  mod test {
    use super::*;

    #[test]
    fn test_index() {}
  }
}

pub mod vectored_slice {
  use super::*;

  #[derive(Debug)]
  pub struct VectoredMatch<'a> {
    pub id: ExpressionIndex,
    pub source: Vec<ByteSlice<'a>>,
    pub flags: ScanFlags,
  }

  pub trait VectorScanner<'data> = FnMut(&VectoredMatch<'data>) -> MatchResult+'data;

  pub(crate) struct VectoredSliceMatcher<'data, 'code> {
    parent_slices: VectoredByteSlices<'data>,
    matched_slices_queue: Mutex<VecDeque<VectoredMatch<'data>>>,
    handler: &'code mut dyn VectorScanner<'data>,
    wakers: Mutex<Vec<Waker>>,
  }

  impl<'data, 'code> VectoredSliceMatcher<'data, 'code> {
    #[inline]
    pub fn new<F: VectorScanner<'data>>(
      parent_slices: &'data [ByteSlice<'data>],
      f: &'code mut F,
    ) -> Self {
      Self {
        parent_slices,
        matched_slices_queue: Mutex::new(VecDeque::new()),
        handler: f,
        wakers: Mutex::new(Vec::new()),
      }
    }

    #[inline(always)]
    const fn parent(&self) -> &'data [ByteSlice<'data>] { self.parent_slices }

    #[inline(always)]
    pub fn pop(&mut self) -> Option<VectoredMatch<'data>> {
      self.matched_slices_queue.lock().pop_front()
    }

    pub fn pop_rest(&mut self) -> Vec<VectoredMatch<'data>> {
      self.matched_slices_queue.lock().drain(..).collect()
    }

    fn find_index_at(
      &self,
      mut column: usize,
      mut within_column_index: usize,
      mut remaining: usize,
    ) -> Option<(usize, usize)> {
      let num_columns = self.parent().len();
      if column >= num_columns {
        return None;
      }
      if remaining == 0 {
        return Some((column, within_column_index));
      }

      let within_column_index = loop {
        let cur_col = self.parent()[column];
        let (prev, max_diff) = if within_column_index > 0 {
          let x = within_column_index;
          within_column_index = 0;
          assert_ne!(cur_col.len(), x);
          (x, cur_col.len() - x)
        } else {
          (0, cur_col.len())
        };
        assert_ne!(max_diff, 0);
        let new_offset = cmp::min(remaining, max_diff);
        let cur_ind = prev + new_offset;
        remaining -= new_offset;
        if remaining == 0 {
          break cur_ind;
        } else if column == (num_columns - 1) {
          return None;
        } else {
          column += 1;
        }
      };

      Some((column, within_column_index))
    }

    fn collect_slices_range(
      &self,
      start: (usize, usize),
      end: (usize, usize),
    ) -> Vec<ByteSlice<'data>> {
      let (start_col, start_ind) = start;
      let (end_col, end_ind) = end;
      assert!(end_col >= start_col);

      if start_col == end_col {
        assert!(end_ind >= start_ind);
        vec![&self.parent()[start_col][start_ind..end_ind]]
      } else {
        let mut ret: Vec<&'data [c_char]> = Vec::with_capacity(end_col - start_col + 1);

        ret.push(&self.parent()[start_col][start_ind..]);
        for cur_col in (start_col + 1)..end_col {
          ret.push(&self.parent()[cur_col]);
        }
        ret.push(&self.parent()[end_col][..end_ind]);
        ret
      }
    }

    pub fn index_range(&self, range: ops::Range<usize>) -> Vec<ByteSlice<'data>> {
      let ops::Range { start, end } = range;
      let (start_col, start_ind) = self.find_index_at(0, 0, start).unwrap();
      let (end_col, end_ind) = self.find_index_at(start_col, start_ind, end).unwrap();
      self.collect_slices_range((start_col, start_ind), (end_col, end_ind))
    }

    #[inline(always)]
    pub fn push_new_match(&mut self, m: VectoredMatch<'data>) {
      self.matched_slices_queue.lock().push_back(m);
      for waker in self.wakers.lock().drain(..) {
        waker.wake();
      }
    }

    #[inline(always)]
    pub fn handle_match(&mut self, m: &VectoredMatch<'data>) -> MatchResult { (self.handler)(m) }

    #[inline(always)]
    pub fn push_waker(&mut self, w: Waker) { self.wakers.lock().push(w); }
  }

  impl<'data, 'code> Future for VectoredSliceMatcher<'data, 'code> {
    type Output = VectoredMatch<'data>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
      if let Some(m) = self.pop() {
        Poll::Ready(m)
      } else {
        self.push_waker(cx.waker().clone());
        Poll::Pending
      }
    }
  }

  pub(crate) unsafe extern "C" fn match_slice_vectored_ref(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    let MatchEvent {
      id,
      range,
      flags,
      context,
    } = MatchEvent::coerce_args(id, from, to, flags, context);
    let mut slice_matcher: Pin<&mut VectoredSliceMatcher> =
      MatchEvent::extract_context::<'_, VectoredSliceMatcher>(context).unwrap();
    let matched_substring = slice_matcher.index_range(range);
    let m = VectoredMatch {
      id,
      source: matched_substring,
      flags,
    };

    let result = slice_matcher.handle_match(&m);
    if result == MatchResult::Continue {
      slice_matcher.push_new_match(m);
    }

    result.into_native()
  }
}

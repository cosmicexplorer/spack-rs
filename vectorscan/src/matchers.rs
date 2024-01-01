/* Copyright 2022-2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Types used in vectorscan match callbacks.
//!
//! # Vectorscan Callback API
//! Vectorscan employs a very different method of generating "matches"; instead
//! of returning a single value from a synchronous search method call, it
//! instead executes a C ABI function pointer referred to as [`match_event_handler()`](https://intel.github.io/hyperscan/dev-reference/api_files.html#c.match_event_handler):
//!
//! ## `match_event_handler()`
//!
//!```c
//! typedef int (*match_event_handler)(
//!   unsigned int id, // expression that matched (0 for single expression)
//!   unsigned long long from, // always 0, if SOM_LEFTMOST is disabled
//!   unsigned long long to,   // index of match end in input
//!   unsigned int flags, // unused
//!   void *context, // context provided by user to vectorscan search methods
//! );
//! ```
//!
//! This crate wraps that C ABI method call to synthesize one of the match
//! result types [`Match`], [`VectoredMatch`], or [`StreamMatch`]. It
//! then provides this input to the user's Rust-level callback method, which
//! returns a [`MatchResult`].
//!
//! ### Advantages
//! This particular API has several advantages over returning a single value:
//! - **Overlapping matches** are much easier to support, because the matching
//!   engine doesn't have to reconstruct its entire state across calls to the
//!   search method (it's a little like a coroutine in this way).
//!   - In particular, the callback method returning [`MatchResult`] (converted
//!     into [`c_int`]) can also be considered to function like a [lisp restart](https://journal.infinitenegativeutility.com/structurally-typed-condition-handling),
//!     a form of coroutine-like control flow in which the user is able to specify which action to
//!     take in response to some runtime condition.
//! - **Stream parsing** is able to use the same API for matching, because the
//!   callback doesn't provide nor require any reference to the string data it
//!   was provided.
//! - **FFI wrappers in other languages (like this crate)** are typically
//!   easier, as **they can figure out how to most efficiently store the matches in their own language**.
//!   In comparison, the [`re2`](https://docs.rs/re2) crate
//!   (also wrapped by this crate's author) required [a separate C++ wrapper](https://github.com/cosmicexplorer/spack-rs/blob/1faa9c32982b4705bc5c9addeb5800d489037dd9/re2/sys/src/c-bindings.hpp#L11)
//!   in order to wrap things like `std::string` or `absl::string_view` with templated or unstable
//!   binary interfaces.
//! - **Complex parsing control flow** can be application-defined in the
//!   callback, instead of requiring vectorscan to provide separate methods for
//!   each type of search. In particular, one supported feature is to **invoke a
//!   separate vectorscan search within the body of a match callback** (although
//!   this has some caveats: see [Minimizing Scratch
//!   Contention](crate::state#minimizing-scratch-contention)), which can be
//!   used to implement higher-level features like capturing groups. Also see
//!   [Synchronous String Scanning] and [Asynchronous String Scanning] for more
//!   on how the callback is extended to support [`async`](https://doc.rust-lang.org/std/keyword.async.html)
//!   use cases.
//!
//! [Synchronous String Scanning]: crate::state::Scratch#synchronous-string-scanning
//! [Asynchronous String Scanning]: crate::state::Scratch#asynchronous-string-scanning
//!
//! ### Assurances
//! Two assurances vectorscan provides which are particularly convenient are:
//! 1. **The match callback will always be invoked synchronously** (although
//!    the results may not always be in order; see [`UnorderedMatchBehavior::AllowsUnordered`](crate::expression::info::UnorderedMatchBehavior::AllowsUnordered)
//!    which can be queried through [`Expression::info()`](crate::expression::Expression::info)).
//!    This means that the callback function may close over mutable state; in Rust terms, it can be
//!    an [`FnMut`] (which with Rust can be converted to a [`dyn`](https://doc.rust-lang.org/std/keyword.dyn.html)
//!    trait to erase the concrete type and use it in the monomorphic C ABI callback method).
//! 2. **The search is complete when `hs_scan()` or other methods return**,
//!    meaning that any state which is closed over by the callback method is no
//!    longer mutably bound, so it can be immediately re-used in another scan.
//!    While stream parsing still requires retaining state across multiple
//!    method calls, Rust's fantastic lifetime system comes into play here, as
//!    the compiler is often able to detect precisely when a [`StreamMatcher`]
//!    is dropped and frees up the closed-over mutable state. For doctests
//!    demonstrating this interaction, please see the higher-level stream
//!    interface in [`crate::stream`] and the doctests for e.g.
//!    [`ScratchStreamSink`](crate::stream::ScratchStreamSink).
//!
//! ## `"catch-unwind"`
//! There is an additional assurance that this crate provides when the
//! `"catch-unwind"` feature is enabled, which is to catch any
//! [`panic`](macro@panic) from the Rust-level callback method and safely
//! re-raise it when vectorscan returns control back to the application, which
//! would otherwise produce undefined behavior (see
//! [`std::panic::catch_unwind()`]). While catching panics previously [caused
//! performance issues for hot-loop function calls in the Servo research browser](https://github.com/rust-lang/rust/issues/34727),
//! this problem was known to be solvable by just generating the LLVM code used
//! for `try`/`catch` in C++, and indeed [Servo's issue was fixed after doing so](https://github.com/rust-lang/rust/pull/67502).
//! In particular, the code now generated is described as having no slowdown
//! for the "happy path" in which no panic occurs.
//!
//! This feature is enabled by default to avoid undefined behavior because of
//! the work that has gone into optimizing this particular use case from the
//! Rust team, but can be disabled if it's found to cause a slowdown in a
//! profile (or Rust can be told to immediately abort upon panic: see
//! [`std::process::abort()`]). However, also note that the [Asynchronous String
//! Scanning] API is another approach provided to decouple the match callback
//! method (which is used only to determine whether to stop matching) from the
//! application's match processing business logic.
//!
//! # This Module
//! The Rust source file generating this documentation contains the
//! `pub(crate) extern "C" unsafe fn` declarations which match the
//! [`match_event_handler()`](#match_event_handler) prototype, but these methods
//! are considered an implementation detail and thus are not exposed by
//! themselves. Instead, the public Rust exports from this file are the inputs
//! and outputs to the match callback function used for different scanning
//! modes:
//! - [`Mode::BLOCK`](crate::flags::Mode::BLOCK): [`Match`] is produced by
//!   [`Scratch::scan_sync()`](crate::state::Scratch::scan_sync), with a single
//!   [`ByteSlice`](crate::sources::ByteSlice) referenced from the input string.
//! - [`Mode::VECTORED`](crate::flags::Mode::VECTORED): [`VectoredMatch`] is
//!   produced by
//!   [`Scratch::scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored),
//!   with the slightly more complex
//!   [`VectoredSubset`](crate::sources::VectoredSubset) used to
//!   represent slices of a
//!   [`VectoredByteSlices`](crate::sources::VectoredByteSlices)
//!   input.
//! - Finally, [`Mode::STREAM`](crate::flags::Mode::STREAM) produces
//!   [`StreamMatch`] for
//!   [`Scratch::scan_sync_stream()`](crate::state::Scratch::scan_sync_stream)
//!   or [`Scratch::flush_eod_sync()`](crate::state::Scratch::flush_eod_sync),
//!   which can only store a [`Range`](crate::sources::Range) as a match may
//!   span across multiple separate inputs, which neither the vectorscan library
//!   nor this crate otherwise retain in order to provide a strict "zero-copy"
//!   interface. While it is possible to provide a [`StreamMatcher`] directly to
//!   [`Scratch::scan_sync_stream()`](crate::state::Scratch::scan_sync_stream),
//!   the higher-level API provided by the [`crate::stream`] module provides a
//!   more restricted interface making use of the separate [`handles`] crate to
//!   manage the more-complex interlocking lifetime requirements of stream
//!   callbacks.

use cfg_if::cfg_if;
use displaydoc::Display;

#[cfg(feature = "catch-unwind")]
use std::{
  any::Any,
  panic::{self, AssertUnwindSafe, RefUnwindSafe, UnwindSafe},
};
use std::{
  fmt, mem, ops,
  os::raw::{c_int, c_uint, c_ulonglong, c_void},
  pin::Pin,
  ptr,
};

/// Reference to the source expression that produced a match result or error.
///
/// This is provided to match results such as [`Match`] as well as errors like
/// [`CompileError`](crate::error::CompileError), although note that its value
/// should be interpreted differently when received as part of a compile error.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ExpressionIndex(
  /// This corresponds to the value of an
  /// [`ExprId`](crate::expression::ExprId) argument provided during expression
  /// set compilation using e.g.
  /// [`ExpressionSet::with_ids()`](crate::expression::ExpressionSet::with_ids).
  ///
  /// This value will be `0` if only a single expression was compiled or if no
  /// expression ids were provided.
  pub c_uint,
);

impl fmt::Display for ExpressionIndex {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "<{}>", self.0) }
}

impl From<c_uint> for ExpressionIndex {
  fn from(x: c_uint) -> Self { Self(x) }
}

impl From<ExpressionIndex> for c_uint {
  fn from(x: ExpressionIndex) -> Self { x.0 }
}

/// Return value for all match callbacks.
///
/// As described in [Advantages](crate::matchers#advantages), this return value
/// can be thought of as a form of lisp restart or other coroutine system,
/// allowing the application to define relatively complex search behavior for
/// any parsing that cannot be expressed with the vectorscan library itself.
#[derive(
  Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, num_enum::IntoPrimitive,
)]
#[repr(u8)]
#[ignore_extra_doc_attributes]
pub enum MatchResult {
  /// Continue matching.
  ///
  /// Most use cases will likely return this value unconditionally from the
  /// callback after storing the match somewhere.
  Continue = 0,
  /// Immediately cease matching.
  ///
  /// In scanning is performed in block or vectored mode and this value is
  /// returned, the scan will simply terminate immediately. If scanning is
  /// performed in streaming mode and this value is returned, any subsequent
  /// calls to
  /// [`Scratch::scan_sync_stream()`](crate::state::Scratch::scan_sync_stream)
  /// or [`ScratchStreamSink::scan()`](crate::stream::ScratchStreamSink::scan)
  /// for the same stream will also immediately return with
  /// [`ScanTerminated`](crate::error::VectorscanRuntimeError::ScanTerminated).
  ///
  /// This is documented to be just any non-zero value at the moment, so **the
  /// current constant value of `1` should not be considered stable!**
  ///
  /// When the `"catch-unwind"` feature is enabled (as it is by default) and the
  /// match callback raises a Rust-level panic, the callback method from this
  /// crate will immediately return with this value to stop the vectorscan
  /// search before re-raising the panic once control returns to Rust code.
  CeaseMatching = 1,
}

impl MatchResult {
  /* TODO: num_enum for const IntoPrimitive! */
  pub(crate) fn into_native(self) -> c_int {
    let x: u8 = self.into();
    x.into()
  }
}

#[derive(Debug)]
pub(crate) struct MatchEvent {
  pub id: ExpressionIndex,
  pub range: ops::Range<usize>,
  pub context: Option<ptr::NonNull<c_void>>,
}

impl MatchEvent {
  pub fn coerce_args(id: c_uint, from: c_ulonglong, to: c_ulonglong, context: *mut c_void) -> Self {
    static_assertions::assert_eq_size!(c_uint, ExpressionIndex);
    static_assertions::const_assert!(mem::size_of::<usize>() >= mem::size_of::<c_ulonglong>());
    static_assertions::assert_eq_size!(ops::Range<usize>, (c_ulonglong, c_ulonglong));
    debug_assert!(from <= to);
    Self {
      id: ExpressionIndex(id),
      range: ops::Range {
        start: from as usize,
        end: to as usize,
      },
      context: ptr::NonNull::new(context),
    }
  }

  pub unsafe fn extract_context<'a, T>(context: ptr::NonNull<c_void>) -> Pin<&'a mut T> {
    Pin::new_unchecked(&mut *mem::transmute::<*mut c_void, *mut T>(
      context.as_ptr(),
    ))
  }
}

pub(crate) mod contiguous_slice {
  use super::*;
  use crate::sources::ByteSlice;

  /// Match object returned when searching a single contiguous string.
  ///
  /// This is returned by e.g.
  /// [`Scratch::scan_sync()`](crate::state::Scratch::scan_sync).
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Match<'a> {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The entire text matching the given pattern.
    ///
    /// This reference is alive for as long as the `'data` lifetime parameter
    /// provided to
    /// [`Scratch::scan_sync()`](crate::state::Scratch::scan_sync), so match
    /// objects can safely be dereferenced and processed after a scan
    /// completes instead of performing complex logic in the match callback
    /// itself. For example, a common pattern is to write the match objects
    /// into some growable array like a [`Vec`] in the callback, then to
    /// process them in bulk when the scan is complete.
    pub source: ByteSlice<'a>,
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub(crate) struct SliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        handler: &'code mut (dyn FnMut(Match<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      pub(crate) struct SliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        handler: &'code mut (dyn FnMut(Match<'data>) -> MatchResult),
      }
    }
  }

  impl<'data, 'code> SliceMatcher<'data, 'code> {
    pub fn new<F: FnMut(Match<'data>) -> MatchResult>(
      parent_slice: ByteSlice<'data>,
      f: &'code mut F,
    ) -> Self {
      let f: &'code mut (dyn FnMut(Match<'data>) -> MatchResult) = f;
      #[cfg(feature = "catch-unwind")]
      let f: &'code mut (dyn FnMut(Match<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(f) };
      Self {
        parent_slice,
        handler: f,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: Match<'data>,
    ) -> Result<MatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: Match<'data>) -> MatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          MatchResult::CeaseMatching
        },
      }
    }

    pub fn handle_match(&mut self, m: Match<'data>) -> MatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.handler)(m)
        }
      }
    }

    pub fn resume_panic(self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  pub(crate) extern "C" fn match_slice(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, context);
    let mut slice_matcher: Pin<&mut SliceMatcher> =
      unsafe { MatchEvent::extract_context(context.unwrap()) };

    if slice_matcher.has_panic() {
      return MatchResult::CeaseMatching.into_native();
    }

    let matched_substring = slice_matcher.index_range(range);
    let m = Match {
      id,
      source: matched_substring,
    };

    let result = slice_matcher.handle_match(m);
    result.into_native()
  }
}
pub use contiguous_slice::Match;

#[cfg(feature = "vectored")]
pub(crate) mod vectored_slice {
  use super::*;
  use crate::sources::{VectoredByteSlices, VectoredSubset};

  /// Match object returned when searching vectored string data.
  ///
  /// This is returned by e.g.
  /// [`Scratch::scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored).
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct VectoredMatch<'a> {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The entire "ragged" subset of vectored string data matching the given
    /// pattern.
    ///
    /// As with [`Match::source`](super::Match::source) for contiguous strings,
    /// this reference is alive for as long as the `'data` lifetime
    /// parameter provided to
    /// [`Scratch::scan_sync_vectored()`](crate::state::Scratch::scan_sync_vectored), and can be
    /// dereferenced and processed after a scan completes. The two lifetime
    /// parameters of [`VectoredSubset`] are collapsed into one here since the
    /// difference between the `'string` and `'slice` lifetimes does not matter
    /// to the search method.
    ///
    /// Note that [`VectoredSubset::iter_slices()`] is the only method this
    /// crate exposes to access subsets of non-contiguous slice data, but the
    /// result can simply be concatenated with
    /// [`[T]::concat()`](prim@slice::concat()) or with [`itertools::concat()`](https://docs.rs/itertools/latest/itertools/fn.concat.html),
    /// at the cost of copying the data. [`VectoredSubset::range`] is
    /// also provided, which is what is used to index into
    /// [`VectoredByteSlices::index_range()`].
    pub source: VectoredSubset<'a, 'a>,
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub(crate) struct VectoredMatcher<'data, 'code> {
        parent_slices: VectoredByteSlices<'data, 'data>,
        handler: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      pub(crate) struct VectoredMatcher<'data, 'code> {
        parent_slices: VectoredByteSlices<'data, 'data>,
        handler: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult),
      }
    }
  }

  impl<'data, 'code> VectoredMatcher<'data, 'code> {
    pub fn new<F: FnMut(VectoredMatch<'data>) -> MatchResult>(
      parent_slices: VectoredByteSlices<'data, 'data>,
      f: &'code mut F,
    ) -> Self {
      let f: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult) = f;
      #[cfg(feature = "catch-unwind")]
      let f: &'code mut (dyn FnMut(VectoredMatch<'data>) -> MatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(f) };
      Self {
        parent_slices,
        handler: f,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn parent_slices(&self) -> VectoredByteSlices<'data, 'data> { self.parent_slices }

    pub fn index_range(&self, range: ops::Range<usize>) -> VectoredSubset<'data, 'data> {
      self.parent_slices.index_range(range).unwrap()
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: VectoredMatch<'data>,
    ) -> Result<MatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: VectoredMatch<'data>) -> MatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          MatchResult::CeaseMatching
        },
      }
    }

    pub fn handle_match(&mut self, m: VectoredMatch<'data>) -> MatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.handler)(m)
        }
      }
    }

    pub fn resume_panic(self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  pub(crate) extern "C" fn match_slice_vectored(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, context);
    let mut slice_matcher: Pin<&mut VectoredMatcher> =
      unsafe { MatchEvent::extract_context(context.unwrap()) };

    if slice_matcher.has_panic() {
      return MatchResult::CeaseMatching.into_native();
    }

    let matched_substring = slice_matcher.index_range(range);
    let m = VectoredMatch {
      id,
      source: matched_substring,
    };

    let result = slice_matcher.handle_match(m);
    result.into_native()
  }
}
#[cfg(feature = "vectored")]
#[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
pub use vectored_slice::VectoredMatch;

#[cfg(feature = "stream")]
#[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
pub(crate) mod stream {
  use super::*;
  use crate::sources::Range;

  // ///```
  // /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
  // tokio_test::block_on(async { /// use vectorscan::{expression::*,
  // matchers::*, flags::*, stream::*}; /// use futures_util::StreamExt;
  // ///
  // /// let expr: Expression = r"\b\w+\b".parse()?;
  // /// let db = expr.compile(
  // ///   Flags::UTF8 | Flags::SOM_LEFTMOST,
  // ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE,
  // /// )?;
  // /// let scratch = db.allocate_scratch()?;
  // ///
  // /// struct S;
  // /// impl StreamScanner for S {
  // ///   fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult {
  // MatchResult::Continue } ///   fn new() -> Self where Self: Sized { Self }
  // ///   fn reset(&mut self) {}
  // ///   fn boxed_clone(&self) -> Box<dyn StreamScanner> { Box::new(Self) }
  // /// }
  // ///
  // /// let mut s = Streamer::open::<S>(&db, scratch.into())?;
  // ///
  // /// let msg1 = "aardvark ";
  // /// s.scan(msg1.as_bytes().into()).await?;
  // ///
  // /// let msg2 = "asdf was a friend ";
  // /// s.scan(msg2.as_bytes().into()).await?;
  // ///
  // /// let msg3 = "after all";
  // /// s.scan(msg3.as_bytes().into()).await?;
  // /// s.flush_eod().await?;
  // /// let rx = s.stream_results();
  // ///
  // /// let msgs: String = [msg1, msg2, msg3].concat();
  // /// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }|
  // &msgs[range]).collect().await; /// assert_eq!(results, vec![
  // ///   "aardvark",
  // ///   "asdf",
  // ///   "was",
  // ///   "a",
  // ///   "friend",
  // ///   "after",
  // ///   "all",
  // /// ]);
  // /// # Ok(())
  // /// # })}
  // /// ```
  /// Match objects returned when searching streaming data.
  ///
  /// This is returned by e.g.
  /// [`Scratch::scan_sync_stream()`](crate::state::Scratch::scan_sync_stream),
  /// [`Scratch::scan_sync_vectored_stream()`](crate::state::Scratch::scan_sync_vectored_stream), or
  /// [`Scratch::flush_eod_sync()`](crate::state::Scratch::flush_eod_sync).
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct StreamMatch {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The start (if [`Flags::SOM_LEFTMOST`]
    /// is provided) and end offsets of the match, with reference to the entire
    /// history of string data that has been provided to this
    /// [`LiveStream`](crate::stream::LiveStream) object.
    ///
    /// [`Flags::SOM_LEFTMOST`]: crate::flags::Flags::SOM_LEFTMOST
    ///
    /// Note that [`LiveStream::reset()`] will reset the stream automaton to
    /// its start state and cause match offsets reported to the callback after
    /// the reset to start once again from 0.
    ///
    /// [`LiveStream::reset()`]: crate::stream::LiveStream::reset
    ///
    /// See the [`crate::stream`] module for a further discussion of how and
    /// when to effectively use the streaming interface, especially how to work
    /// around not being able to reference the contents of the original data
    /// stream.
    pub range: Range,
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      /// A struct holding a reference with the `&'code` lifetime to a [`dyn`](https://doc.rust-lang.org/std/keyword.dyn.html)
      /// `FnMut`, which is a type-erased vtable.
      pub struct StreamMatcher<'code> {
        handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+UnwindSafe+RefUnwindSafe+'code),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      /// A struct holding a reference with the `&'code` lifetime to a [`dyn`](https://doc.rust-lang.org/std/keyword.dyn.html)
      /// `FnMut`, which is a type-erased vtable.
      #[repr(transparent)]
      pub struct StreamMatcher<'code> {
        handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+'code),
      }
    }
  }

  impl<'code> StreamMatcher<'code> {
    /// Create a matcher instance which wraps the provided `dyn` vtable
    /// reference.
    ///
    /// Any variables closed over by a closure reference provided to `handler`
    /// will become available again after this object is dropped (which must
    /// occur within the span of the `'code` lifetime parameter), so any state
    /// which is modified by a match callback can be examined once the
    /// stream is dropped!
    pub fn new(handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+'code)) -> Self {
      #[cfg(feature = "catch-unwind")]
      let handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+UnwindSafe+RefUnwindSafe+'code) =
        unsafe { mem::transmute(handler) };
      Self {
        handler,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub(crate) fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: StreamMatch,
    ) -> Result<MatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: StreamMatch) -> MatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          MatchResult::CeaseMatching
        },
      }
    }

    pub(crate) fn handle_match(&mut self, m: StreamMatch) -> MatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.handler)(m)
        }
      }
    }

    pub(crate) fn resume_panic(&mut self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload.take() {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  #[repr(transparent)]
  pub(crate) struct SendStreamMatcher<'code>(StreamMatcher<'code>);

  impl<'code> SendStreamMatcher<'code> {
    pub fn new(handler: &'code mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code)) -> Self {
      Self(StreamMatcher::new(handler))
    }

    pub fn as_mut_basic(&mut self) -> &mut StreamMatcher<'code> { unsafe { mem::transmute(self) } }
  }

  static_assertions::assert_eq_size!(
    &'static mut (dyn FnMut(StreamMatch) -> MatchResult+Send),
    &'static mut (dyn FnMut(StreamMatch) -> MatchResult)
  );
  static_assertions::assert_eq_size!(StreamMatcher<'static>, SendStreamMatcher<'static>);

  unsafe impl<'code> Send for SendStreamMatcher<'code> {}

  pub(crate) extern "C" fn match_slice_stream(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    context: *mut c_void,
  ) -> c_int {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let MatchEvent { id, range, context } = MatchEvent::coerce_args(id, from, to, context);
    let mut matcher: Pin<&mut StreamMatcher> =
      unsafe { MatchEvent::extract_context(context.unwrap()) };

    if matcher.has_panic() {
      return MatchResult::CeaseMatching.into_native();
    }

    let m = StreamMatch {
      id,
      range: range.into(),
    };

    let result = matcher.handle_match(m);
    result.into_native()
  }
}
#[cfg(feature = "stream")]
#[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
pub use stream::{StreamMatch, StreamMatcher};

/// Types used in chimera match callbacks.
///
/// # Tradeoffs with Vectorscan for PCRE
/// The chimera library does not support several features of the base vectorscan
/// library (including vectored or stream parsing) in order to implement full
/// support for PCRE patterns, including **capture groups**, which typically
/// must be implemented with some form of recursive searching in the base
/// vectorscan library (see [Minimizing Scratch Contention]). These features may
/// be able to replace multiple separate vectorscan calls, at the cost of [some
/// performance].
///
/// [Minimizing Scratch Contention]: crate::state#minimizing-scratch-contention
/// [some performance]: https://intel.github.io/hyperscan/dev-reference/chimera.html#scanning
///
/// So while the chimera matching interface is generally smaller and less
/// complex than vectorscan, the library still avoids unbounded computation from
/// exponential blowup by explicitly [handling PCRE failure cases]. That means
/// it needs two match callbacks instead of one:
///
/// [handling PCRE failure cases]: https://intel.github.io/hyperscan/dev-reference/chimera.html#handling-runtime-errors
///
/// ## [`ch_match_event_handler()`](https://intel.github.io/hyperscan/dev-reference/chimera.html#c.ch_match_event_handler)
///
///```c
/// typedef ch_callback_t (*ch_match_event_handler)(
///   unsigned int id, // expression that matched (0 for single expression)
///   unsigned long long from, // index of match start in input
///   unsigned long long to,   // index of match end in input
///   unsigned int flags,  // unused
///   unsigned int size, // number of capture groups (0 if NOGROUPS is used)
///   const ch_capture_t *captured, // pointer to array of capture groups
///   void *ctx, // context provided by user to chimera search method
/// );
/// ```
///
/// This callback receives a
/// [`ChimeraMatch`](crate::matchers::chimera::ChimeraMatch) object and returns
/// a [`ChimeraMatchResult`](crate::matchers::chimera::ChimeraMatchResult),
/// similar to the vectorscan library's match callbacks.
///
/// ## [`ch_error_event_handler()`](https://intel.github.io/hyperscan/dev-reference/chimera.html#c.ch_error_event_handler)
///
///```c
/// typedef ch_callback_t (*ch_error_event_handler)(
///   ch_error_event_t error_type, // the variant of PCRE error
///   unsigned int id, // expression that caused the error
///   void *info, // unused
///   void *ctx, // context provided by user to chimera search method
/// );
/// ```
///
/// This callback receives a
/// [`ChimeraMatchError`](crate::error::chimera::ChimeraMatchError) object and
/// also returns a
/// [`ChimeraMatchResult`](crate::matchers::chimera::ChimeraMatchResult).
/// Depending on your use case, regular expressions that exceed these PCRE
/// limits may or may not be useful matches, so you can choose to ignore them
/// with [`ChimeraMatchResult::Continue`](crate::matchers::chimera::ChimeraMatchResult::Continue)
/// or immediately cease matching with
/// [`ChimeraMatchResult::Terminate`](crate::matchers::chimera::ChimeraMatchResult::Terminate).
/// The PCRE limits may be configured for a particular database using
/// [`ChimeraExpressionSet::with_limits()`](crate::expression::chimera::ChimeraExpressionSet::with_limits).
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;
  use crate::{error::chimera::*, hs, sources::ByteSlice};

  use smallvec::SmallVec;

  use std::{hash, slice};

  /// Return value for all chimera match callbacks.
  ///
  /// Note that this type also has the [`Self::SkipPattern`] case, which has no
  /// analogue in the base vectorscan library's [`super::MatchResult`].
  #[derive(
    Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, num_enum::IntoPrimitive,
  )]
  #[repr(u8)]
  #[ignore_extra_doc_attributes]
  pub enum ChimeraMatchResult {
    /// Continue matching.
    Continue = hs::CH_CALLBACK_CONTINUE,
    /// Terminate matching.
    ///
    /// When the `"catch-unwind"` feature is enabled (as it is by default) and
    /// the match callback raises a Rust-level panic, the callback method
    /// from this crate will immediately return with this value to stop the
    /// chimera search before re-raising the panic once control returns
    /// to Rust code.
    Terminate = hs::CH_CALLBACK_TERMINATE,
    /// Skip remaining matches for this ID and continue.
    SkipPattern = hs::CH_CALLBACK_SKIP_PATTERN,
  }

  impl ChimeraMatchResult {
    /* TODO: num_enum for const IntoPrimitive! */
    pub(crate) fn into_native(self) -> hs::ch_callback_t {
      let x: u8 = self.into();
      x.into()
    }
  }

  #[derive(Debug)]
  struct ChimeraMatchEvent<'a> {
    pub id: ExpressionIndex,
    pub range: ops::Range<usize>,
    pub captures: Option<&'a [hs::ch_capture]>,
    pub context: Option<ptr::NonNull<c_void>>,
  }

  impl<'a> ChimeraMatchEvent<'a> {
    pub fn coerce_args(
      id: c_uint,
      from: c_ulonglong,
      to: c_ulonglong,
      size: c_uint,
      captured: *const hs::ch_capture,
      context: *mut c_void,
    ) -> Self {
      debug_assert!(from <= to);
      Self {
        id: ExpressionIndex(id),
        range: ops::Range {
          start: from as usize,
          end: to as usize,
        },
        captures: if captured.is_null() || size == 0 {
          None
        } else {
          Some(unsafe { slice::from_raw_parts(captured, size as usize) })
        },
        context: ptr::NonNull::new(context),
      }
    }

    pub unsafe fn extract_context<'c, T>(context: ptr::NonNull<c_void>) -> Pin<&'c mut T> {
      MatchEvent::extract_context(context)
    }
  }

  /// Match object returned when searching a single contiguous string.
  ///
  /// This is returned by e.g.
  /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync).
  /// Note that unlike e.g. [`super::Match`], this does not implement [`Copy`],
  /// as it may need to keep track of owned heap data in [`Self::captures`].
  /// However, if
  /// [`ChimeraMode::NOGROUPS`](crate::flags::chimera::ChimeraMode::NOGROUPS) is
  /// used, [`Self::captures`] will always be [`None`], and `.clone()` can be
  /// called without any heap allocation. As an additional optimization,
  /// patterns with up to 19 capturing groups (the 0th group being the entire
  /// match) are stored on the stack with [`smallvec`].
  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
  pub struct ChimeraMatch<'a> {
    /// ID of matched expression, or `0` if unspecified.
    pub id: ExpressionIndex,
    /// The entire text matching the given pattern.
    ///
    /// As with [`super::Match`], this reference is alive for as long as the
    /// `'data` lifetime parameter provided to
    /// [`ChimeraScratch::scan_sync()`](crate::state::chimera::ChimeraScratch::scan_sync), so match
    /// objects can safely be dereferenced and processed after a scan
    /// completes instead of performing complex logic in the match callback
    /// itself. For example, a common pattern is to write the match objects
    /// into some growable array like a [`Vec`] in the callback, then to
    /// process them in bulk when the scan is complete.
    pub source: ByteSlice<'a>,
    /// Captured text, if
    /// [`ChimeraMode::GROUPS`](crate::flags::chimera::ChimeraMode::GROUPS) was
    /// specified during compilation (otherwise [`None`]).
    ///
    /// Individual captures are themselves optional because of patterns like
    /// `"hell(o)?"`, which would produce [`None`] for the 1st capture if
    /// the pattern `o` isn't matched. Using [`Option`] here lets us distinguish
    /// a non-matching capture group from a capture group that matched the
    /// empty string. The 0th capture always corresponds to the entire match
    /// text, so it is always [`Some`] and should always be
    /// equal to [`Self::source`].
    pub captures: Option<SmallVec<Option<ByteSlice<'a>>, 20>>,
  }

  impl<'a> hash::Hash for ChimeraMatch<'a> {
    fn hash<H>(&self, state: &mut H)
    where H: hash::Hasher {
      self.id.hash(state);
      self.source.hash(state);
      if let Some(ref captures) = self.captures {
        captures[..].hash(state);
      }
    }
  }

  cfg_if! {
    if #[cfg(feature = "catch-unwind")] {
      pub(crate) struct ChimeraSliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        match_handler: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe),
        error_handler: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe),
        panic_payload: Option<Box<dyn Any+Send>>,
      }
    } else {
      pub(crate) struct ChimeraSliceMatcher<'data, 'code> {
        parent_slice: ByteSlice<'data>,
        match_handler: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult),
        error_handler: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult),
      }
    }
  }

  impl<'data, 'code> ChimeraSliceMatcher<'data, 'code> {
    pub fn new(
      parent_slice: ByteSlice<'data>,
      matcher: &'code mut impl FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult,
      error: &'code mut impl FnMut(ChimeraMatchError) -> ChimeraMatchResult,
    ) -> Self {
      let matcher: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult) = matcher;
      #[cfg(feature = "catch-unwind")]
      let matcher: &'code mut (dyn FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(matcher) };
      let error: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult) = error;
      #[cfg(feature = "catch-unwind")]
      let error: &'code mut (dyn FnMut(ChimeraMatchError) -> ChimeraMatchResult+UnwindSafe+RefUnwindSafe) =
        unsafe { mem::transmute(error) };
      Self {
        parent_slice,
        match_handler: matcher,
        error_handler: error,
        #[cfg(feature = "catch-unwind")]
        panic_payload: None,
      }
    }

    pub fn parent_slice(&self) -> ByteSlice<'data> { self.parent_slice }

    pub fn index_range(&self, range: ops::Range<usize>) -> ByteSlice<'data> {
      self.parent_slice.index_range(range).unwrap()
    }

    pub fn has_panic(&self) -> bool {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.panic_payload.is_some()
        } else {
          false
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_with_panic(
      &mut self,
      m: ChimeraMatch<'data>,
    ) -> Result<ChimeraMatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.match_handler);
      panic::catch_unwind(move || f(m))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_match_wrapping_panic(&mut self, m: ChimeraMatch<'data>) -> ChimeraMatchResult {
      match self.handle_match_with_panic(m) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          ChimeraMatchResult::Terminate
        },
      }
    }

    pub fn handle_match(&mut self, m: ChimeraMatch<'data>) -> ChimeraMatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_match_wrapping_panic(m)
        } else {
          (self.match_handler)(m)
        }
      }
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_error_with_panic(
      &mut self,
      e: ChimeraMatchError,
    ) -> Result<ChimeraMatchResult, Box<dyn Any+Send>> {
      let mut f = AssertUnwindSafe(&mut self.error_handler);
      panic::catch_unwind(move || f(e))
    }

    #[cfg(feature = "catch-unwind")]
    fn handle_error_wrapping_panic(&mut self, e: ChimeraMatchError) -> ChimeraMatchResult {
      match self.handle_error_with_panic(e) {
        Ok(result) => result,
        Err(e) => {
          self.panic_payload = Some(e);
          ChimeraMatchResult::Terminate
        },
      }
    }

    pub fn handle_error(&mut self, e: ChimeraMatchError) -> ChimeraMatchResult {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          self.handle_error_wrapping_panic(e)
        } else {
          (self.error_handler)(e)
        }
      }
    }

    pub fn resume_panic(self) {
      cfg_if! {
        if #[cfg(feature = "catch-unwind")] {
          if let Some(err) = self.panic_payload {
            panic::resume_unwind(err);
          }
        }
      }
    }
  }

  pub(crate) extern "C" fn match_chimera_slice(
    id: c_uint,
    from: c_ulonglong,
    to: c_ulonglong,
    flags: c_uint,
    size: c_uint,
    captured: *const hs::ch_capture,
    context: *mut c_void,
  ) -> hs::ch_callback_t {
    debug_assert_eq!(flags, 0, "flags are currently unused");
    let ChimeraMatchEvent {
      id,
      range,
      captures,
      context,
    } = ChimeraMatchEvent::coerce_args(id, from, to, size, captured, context);
    let mut matcher: Pin<&mut ChimeraSliceMatcher> =
      unsafe { ChimeraMatchEvent::extract_context(context.unwrap()) };

    if matcher.has_panic() {
      return ChimeraMatchResult::Terminate.into_native();
    }

    let matched_substring = matcher.index_range(range);
    let m = ChimeraMatch {
      id,
      source: matched_substring,
      captures: captures.map(|c| {
        c.iter()
          .map(|hs::ch_capture { flags, from, to }| {
            if *flags == hs::CH_CAPTURE_FLAG_INACTIVE as c_uint {
              None
            } else {
              debug_assert_eq!(*flags, hs::CH_CAPTURE_FLAG_ACTIVE as c_uint);
              debug_assert!(from <= to);
              let range = ops::Range {
                start: *from as usize,
                end: *to as usize,
              };
              Some(matcher.index_range(range))
            }
          })
          .collect()
      }),
    };

    let result = matcher.handle_match(m);
    result.into_native()
  }

  pub(crate) extern "C" fn error_callback_chimera(
    error_type: hs::ch_error_event_t,
    id: c_uint,
    info: *mut c_void,
    ctx: *mut c_void,
  ) -> hs::ch_callback_t {
    let error_type = ChimeraMatchErrorType::from_native(error_type);
    let id = ExpressionIndex(id);
    debug_assert!(info.is_null(), "info pointer is currently unused");
    let ctx = ptr::NonNull::new(ctx);
    let mut matcher: Pin<&mut ChimeraSliceMatcher> =
      unsafe { ChimeraMatchEvent::extract_context(ctx.unwrap()) };

    if matcher.has_panic() {
      return ChimeraMatchResult::Terminate.into_native();
    }

    let e = ChimeraMatchError { error_type, id };

    let result = matcher.handle_error(e);
    result.into_native()
  }
}

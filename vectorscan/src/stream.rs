/* Copyright 2022-2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Higher-level wrappers to manage state needed for stream parsing.
//!
//! # Stream Parsing
//! "Stream parsing", which in this case refers simply to "matching a pattern
//! against a non-contiguous data stream" (like a pipe), is surprisingly poorly
//! supported by most regex engines as well as higher-level parsers. Most of the
//! time, this is the correct tradeoff to make, as many more optimizations are
//! available for contiguous string search, and in practice many
//! non-contiguous streams can be "tokenized" beforehand e.g. by splitting them
//! into lines, or some other sentinel character known not to appear in any of
//! the input patterns such as a null byte.
//!
//! ## Stream Parsing for Correctness
//! However, it should also be noted that these heuristic methods for
//! tokenization may suddenly break, especially if the application is receiving
//! uncontrolled user input (and therefore can't rely on identifying sentinel
//! characters). Additionally, as discussed in [Advantages], many other regex
//! engines simply find it much more difficult to support interruptible use
//! cases like stream parsing, because they return a single synchronous result
//! instead of using vectorscan's coroutine-like match callback API. This is
//! also why vectorscan is more easily able to report *overlapping matches*,
//! which also improves correctness in that longest-match semantics don't have
//! to be explicitly opted out of.
//!
//! [Advantages]: crate::matchers#advantages
//!
//! ## Stream Parsing for Performance
//! *TODO: citation for this entire paragraph!*
//! Intel primarily designed the hyperscan library's stream parsing
//! functionality for extremely low-latency network traffic analysis. This may
//! involve:
//! - quite large amounts of data, such that tokenizing the data into lines or
//!   generally copying/moving it at all introduces an unacceptable level of
//!   latency (this is why even the smallest `SOM_LEFTMOST` horizon size
//!   [`Mode::SOM_HORIZON_SMALL`] still stores start-of-match offsets within the
//!   last 2^16 bytes!),
//! - received over the network in unpredictable bursts,
//! - in which the data stream cannot be reordered or split up,
//! - with patterns that are often expected to span multiple separate
//!   non-contiguous chunks of data in order to match,
//! - where it's often more important to be able to know *what pattern* was
//!   matched (e.g. to classify input packets) than to know the *precise input
//!   string* that matched it.
//!
//! [`Mode::SOM_HORIZON_SMALL`]: crate::flags::Mode::SOM_HORIZON_SMALL
//!
//! These unusual constraints led Intel to invest in stream parsing, but this
//! author would love to see it supported by more regex engines and parsing
//! frameworks in the future, because **correctly matching patterns that span
//! non-contiguous input is really difficult to solve outside of the regex
//! engine**!
//!
//! ## Workarounds to Reference Streamed Data
//! Because streaming matches may span any number of individual contiguous
//! inputs, neither the vectorscan library nor this crate make any
//! attempt to preserve any reference to the original string data, as part
//! of a "zero-copy" interface. However, this means that the
//! application performing stream parsing can tee the stream input
//! elsewhere while feeding it to vectorscan (perhaps in a compacted form),
//! and only needs to pull out that lookup mechanism if needed to perform
//! further processing on a match that depends on the match's string
//! contents. When performing this strategy, enabling
//! [`Flags::SOM_LEFTMOST`] (as it is by default) is recommended to reduce the
//! cost of reconstructing the match string, at the cost of
//! slightly lower scan performance.
//!
//! [`Flags::SOM_LEFTMOST`]: crate::flags::Flags::SOM_LEFTMOST
//!
//! ### Doing Work at Compile Time to Minimize Need for Stream Data
//! However, before looking into complex mechanisms to keep data around so
//! it can be queried later, keep in mind that the vectorscan library
//! makes a great deal of effort to support complex search queries at
//! "compile time" using features like [`ExpressionSet::with_ids()`] to
//! identify matched sub-patterns, or [`Flags::COMBINATION`] to generate
//! complex acceptance criteria for matching a pattern. If possible, a scan
//! should be performed so that only tracking matches for
//! [`StreamMatch::id`] is necessary, with
//! [`StreamMatch::range`] being used at most to *order* the matches instead of
//! to look up their data.
//!
//! [`ExpressionSet::with_ids()`]: crate::expression::ExpressionSet::with_ids
//! [`Flags::COMBINATION`]: crate::flags::Flags::COMBINATION
//! [`StreamMatch::id`]: crate::matchers::StreamMatch::id
//! [`StreamMatch::range`]: crate::matchers::StreamMatch::range
//!
//! ## Performance Considerations
//! Stream parsing [disables several search optimizations], so even the
//! Intel documentation recommends using [`Mode::BLOCK`] (which returns
//! [`Match`] in this crate) where possible for best performance.
//!
//! [Advantages]: crate::matchers#advantages
//! [disables several search optimizations]: https://intel.github.io/hyperscan/dev-reference/performance.html#block-based-matching
//! [`Mode::BLOCK`]: crate::flags::Mode::BLOCK
//! [`Match`]: crate::matchers::Match
//!
//! # This Module
//! While creating a [`LiveStream`] is really the only part truly required to
//! perform stream searching with [`Scratch::scan_sync_stream()`], most of this
//! module is instead taken up by wrapper structs which combine the
//! [`LiveStream`] object itself with [`StreamMatcher`] and [`Scratch`]
//! instances, making use of [`handles`] to select different lazy vs eager
//! cloning techniques. This decoupling allows [`ScratchStreamSink::scan()`] to
//! provide the nice and easy API we're used to from other regex engines:
//!
//!```
//! #[cfg(feature = "compiler")]
//! fn main() -> Result<(), vectorscan::error::VectorscanError> {
//!   use vectorscan::{expression::*, flags::*, stream::*, state::*, matchers::*};
//!   use std::ops::Range;
//!
//!   let expr: Expression = "a+".parse()?;
//!   let block_db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
//!   let stream_db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
//!   let mut scratch = Scratch::blank();
//!   scratch.setup_for_db(&block_db)?;
//!   scratch.setup_for_db(&stream_db)?;
//!   let live = stream_db.allocate_stream()?;
//!
//!   // With the non-streaming API, we only need to provide the scratch space and db:
//!   let mut matches: Vec<&str> = Vec::new();
//!   scratch
//!     .scan_sync(&block_db, "aardvarka".into(), |m| {
//!       matches.push(unsafe { m.source.as_str() });
//!       MatchResult::Continue
//!     })?;
//!   assert_eq!(&matches, &["a", "aa", "a", "a"]);
//!
//!   // With the streaming API, we need a little more setup:
//!   // Create the `matches` vector which is mutably captured in the dyn closure.
//!   let mut matches: Vec<StreamMatch> = Vec::new();
//!   // Capture `matches` into `match_fn`;
//!   // in this case, `match_fn` is an unboxed stack-allocated closure.
//!   let mut match_fn = |m| {
//!     matches.push(m);
//!     MatchResult::Continue
//!   };
//!   // Create a scope to mutably borrow `match_fn` in:
//!   {
//!     // `matcher` now keeps the reference to `matches` alive
//!     // in rustc's local lifetime tracking via `match_fn`.
//!     let matcher = StreamMatcher::new(&mut match_fn);
//!     let mut sink = ScratchStreamSink::new(live, matcher, scratch);
//!
//!     // After all this setup, now we have our nice fluent API!
//!     sink.scan("aardvarka".into())?;
//!     sink.scan("a".into())?;
//!     // Streams must explicitly mark the end of data.
//!     sink.flush_eod()?;
//!   }
//!   // This will also drop `matcher`, which means `match_fn`
//!   // holds the only reference to `matches`.
//!   // We could also have used `mem::drop()` explicitly.
//!
//!   // Since `match_fn` is otherwise unused outside of `matcher`,
//!   // rustc can statically determine that no other mutable reference
//!   // to `matches` exists, so it "unlocks" the value
//!   // and lets us consume it with `.into_iter()`.
//!   let matches: Vec<Range<usize>> = matches
//!     .into_iter()
//!     .map(|m| m.range.into())
//!     .collect();
//!   // The `8..10` match crossed our two non-contiguous inputs!
//!   assert_eq!(&matches, &[0..1, 0..2, 5..6, 8..9, 8..10]);
//!   Ok(())
//! }
//! # #[cfg(not(feature = "compiler"))]
//! # fn main() {}
//! ```

#[cfg(feature = "vectored")]
use crate::sources::vectored::VectoredByteSlices;
use crate::{
  database::Database,
  error::{CompressionError, VectorscanRuntimeError},
  hs,
  matchers::stream::StreamMatcher,
  sources::ByteSlice,
  state::Scratch,
};

use handles::{Handle, Resource};

use std::{ops, ptr};

/// Pointer type for stream allocations used in [`LiveStream#Managing
/// Allocations`](LiveStream#managing-allocations).
pub type NativeStream = hs::hs_stream;

/// Stateful stream object initialized against some [`Database`].
///
/// While this type can be provided directly to methods such as
/// [`Scratch::scan_sync_stream()`], the other structs in this module wrap it in
/// a type-erased [`Handle`] as a way to swap out whether lazy or eager cloning
/// strategies are used.
#[derive(Debug)]
#[repr(transparent)]
pub struct LiveStream(*mut NativeStream);

unsafe impl Send for LiveStream {}

/// # Stream Operations
/// After creation, the stream can be written to, but doing so
/// requires providing an additional match callback, which is the job of structs
/// like [`ScratchStreamSink`]. Instead, this struct provides [`Self::reset()`]
/// and [`Self::compress()`] to modify or serialize the instantaneous stream
/// state, neither of which require invoking a match callback.
impl LiveStream {
  /// Initialize a new live stream object into a newly allocated memory region.
  ///
  /// The stream will be set to the initial automaton state, with match offsets
  /// starting at 0.
  pub fn open(db: &Database) -> Result<Self, VectorscanRuntimeError> {
    let mut ret = ptr::null_mut();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_open_stream(
        db.as_ref_native(),
        /* NB: ignoring flags for now! */
        0,
        &mut ret,
      )
    })?;
    Ok(unsafe { Self::from_native(ret) })
  }

  /// Reset this stream's automaton state to the initial state, and restart
  /// match offsets at 0.
  pub fn reset(&mut self) -> Result<(), VectorscanRuntimeError> {
    VectorscanRuntimeError::from_native(unsafe { hs::hs_direct_reset_stream(self.as_mut_native()) })
  }

  /// Write the stream's current state into a buffer according to the `into`
  /// strategy.
  ///
  /// The stream can later be deserialized from this state into a working
  /// in-memory stream again with methods such as
  /// [`compress::CompressedStream::expand()`].
  pub fn compress(
    &self,
    into: compress::CompressReserveBehavior,
  ) -> Result<compress::CompressedStream, CompressionError> {
    compress::CompressedStream::compress(into, self)
  }
}

/// # Managing Allocations
/// These methods provide access to the underlying memory allocation containing
/// the data for the in-memory stream. They can be used along with
/// [`compress::CompressedStream::expand_into_at()`] to control the memory
/// location used for the stream, or to preserve stream allocations across
/// weird lifetime constraints.
///
/// Note that [`Database::stream_size()`] can be used to determine the size of
/// the memory allocation pointed to by [`Self::as_ref_native()`] and
/// [`Self::as_mut_native()`], but (**FIXME?**) there is currently no method
/// provided by the vectorscan library to get the stream's allocation size from
/// the stream object itself.
impl LiveStream {
  /// Wrap the provided allocation `p`.
  ///
  /// # Safety
  /// The pointer `p` must point to an initialized db allocation prepared by
  /// [`Self::open()`] or [`compress::CompressedStream::expand_into_at()`]!
  ///
  /// This method also makes it especially easy to create multiple references to
  /// the same allocation, which will then cause a double free when
  /// [`Self::try_drop()`] is called more than once for the same db allocation.
  /// To avoid that issue, you can wrap the result in a
  /// [`ManuallyDrop`](std::mem::ManuallyDrop); but
  /// unlike [`Database::from_native()`], a stream is a mutable object, so
  /// multiple copies of it will break Rust's ownership rules:
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, matchers::*, stream::*};
  ///   use std::{mem::ManuallyDrop, ops::Range};
  ///
  ///   // Compile a legitimate stream:
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(
  ///     Flags::SOM_LEFTMOST,
  ///     Mode::STREAM | Mode::SOM_HORIZON_LARGE
  ///   )?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///   let mut stream = db.allocate_stream()?;
  ///
  ///   // Create two new references to that allocation,
  ///   // wrapped to avoid calling the drop code:
  ///   let stream_ptr: *mut NativeStream = stream.as_mut_native();
  ///   let mut stream_ref_1 = ManuallyDrop::new(unsafe { LiveStream::from_native(stream_ptr) });
  ///   let mut stream_ref_2 = ManuallyDrop::new(unsafe { LiveStream::from_native(stream_ptr) });
  ///
  ///   // Both stream references are valid and can be used for matching.
  ///
  ///   let mut matches: Vec<Range<usize>> = Vec::new();
  ///   let mut match_fn = |StreamMatch { range, .. }| {
  ///     matches.push(range.into());
  ///     MatchResult::Continue
  ///   };
  ///   let mut matcher = StreamMatcher::new(&mut match_fn);
  ///   scratch
  ///     .scan_sync_stream(&mut stream_ref_1, &mut matcher, "aardvarka".into())?;
  ///   scratch
  ///     .scan_sync_stream(&mut stream_ref_2, &mut matcher, "aardvarka".into())?;
  ///   // The 8..11 demonstrates that this was actually the same mutable stream!
  ///   assert_eq!(&matches, &[0..1, 0..2, 5..6, 8..9, 8..10, 8..11, 14..15, 17..18]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub const unsafe fn from_native(p: *mut NativeStream) -> Self { Self(p) }

  /// Get a read-only reference to the stream allocation.
  ///
  /// This method is mostly used internally and cast to a pointer to provide to
  /// the vectorscan native library methods.
  pub fn as_ref_native(&self) -> &NativeStream { unsafe { &*self.0 } }

  /// Get a mutable reference to the stream allocation.
  ///
  /// The result of this method can be cast to a pointer and provided to
  /// [`Self::from_native()`].
  pub fn as_mut_native(&mut self) -> &mut NativeStream { unsafe { &mut *self.0 } }

  /// Generate a new stream in a newly allocated memory region which matches the
  /// same db.
  ///
  /// The stream will be set to the initial automaton state.
  pub fn try_clone(&self) -> Result<Self, VectorscanRuntimeError> {
    let mut ret = ptr::null_mut();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_copy_stream(&mut ret, self.as_ref_native())
    })?;
    Ok(unsafe { Self::from_native(ret) })
  }

  /// Reset the stream state to the same as that of `source`.
  ///
  /// # Safety
  /// `self` and `source` must have been originally opened against the same db
  /// (meaning the same compiled database, not necessarily the same db
  /// allocation)!
  pub unsafe fn try_clone_from(&mut self, source: &Self) -> Result<(), VectorscanRuntimeError> {
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_direct_reset_and_copy_stream(self.as_mut_native(), source.as_ref_native())
    })
  }

  /// Free the underlying stream allocation.
  ///
  /// # Safety
  /// This method must be called at most once over the lifetime of each stream
  /// allocation. It is called by default on drop, so
  /// [`ManuallyDrop`](std::mem::ManuallyDrop) is recommended to wrap instances
  /// that reference external data in order to avoid attempting to free the
  /// referenced data.
  ///
  /// ## Only Frees Memory
  /// This method performs no processing other than freeing the allocated
  /// memory, so it can be skipped without leaking resources if the
  /// underlying [`NativeStream`] allocation is freed by some other means.
  pub unsafe fn try_drop(&mut self) -> Result<(), VectorscanRuntimeError> {
    VectorscanRuntimeError::from_native(unsafe { hs::hs_direct_free_stream(self.as_mut_native()) })
  }
}

/// NB: [`Clone::clone_from()`] is not implemented because
/// [`Self::try_clone_from()`] is unsafe!
impl Clone for LiveStream {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl Resource for LiveStream {
  type Error = VectorscanRuntimeError;

  fn deep_clone(&self) -> Result<Self, Self::Error> { self.try_clone() }

  fn deep_boxed_clone(&self) -> Result<Box<dyn Resource<Error=Self::Error>>, Self::Error> {
    Ok(Box::new(self.try_clone()?))
  }

  unsafe fn sync_drop(&mut self) -> Result<(), Self::Error> { self.try_drop() }
}

impl ops::Drop for LiveStream {
  fn drop(&mut self) {
    unsafe {
      self.try_drop().unwrap();
    }
  }
}

/// A wrapper around all the state needed to execute a stream search.
///
/// By holding handles to [`Self::live`] and [`Self::scratch`], the stream
/// scanning API can be made quite fluent, without as many parameters per call:
///
///```
/// #[cfg(feature = "compiler")]
/// fn main() -> Result<(), vectorscan::error::VectorscanError> {
///   use vectorscan::{expression::*, flags::*, stream::*, matchers::*};
///   use std::{ops::Range, mem};
///
///   let expr: Expression = "a+".parse()?;
///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
///   let scratch = db.allocate_scratch()?;
///   let live = db.allocate_stream()?;
///
///   // Create the `matches` vector which is mutably captured in the dyn closure.
///   let mut matches: Vec<StreamMatch> = Vec::new();
///   // Capture `matches` into `match_fn`;
///   // in this case, `match_fn` is an unboxed stack-allocated closure.
///   let mut match_fn = |m| {
///     matches.push(m);
///     MatchResult::Continue
///   };
///   // `matcher` now keeps the reference to `matches` alive
///   // in rustc's local lifetime tracking.
///   let matcher = StreamMatcher::new(&mut match_fn);
///   let mut sink = ScratchStreamSink::new(live, matcher, scratch);
///
///   sink.scan("aardvark".into())?;
///   sink.flush_eod()?;
///
///   // This will also drop `matcher`, which means `match_fn`
///   // holds the only reference to `matches`.
///   mem::drop(sink);
///   // This could also be performed by explicitly
///   // introducing a scope with `{}`.
///
///   // Since `match_fn` is otherwise unused outside of `matcher`,
///   // rustc can statically determine that no other mutable reference
///   // to `matches` exists, so it "unlocks" the value
///   // and lets us consume it with `.into_iter()`.
///   let matches: Vec<Range<usize>> = matches
///     .into_iter()
///     .map(|m| m.range.into())
///     .collect();
///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
///   Ok(())
/// }
/// # #[cfg(not(feature = "compiler"))]
/// # fn main() {}
/// ```
pub struct ScratchStreamSink<'code> {
  /// Cloneable handle to a stateful stream.
  pub live: Box<dyn Handle<R=LiveStream>>,
  /// Type-erased wrapper over the user-provided match callback.
  pub matcher: StreamMatcher<'code>,
  /// Cloneable handle to a scratch space initialized for the same db as
  /// [`Self::live`].
  pub scratch: Box<dyn Handle<R=Scratch>>,
}

impl<'code> ScratchStreamSink<'code> {
  /// Collate all the state necessary to match against a stream.
  pub fn new(
    live: impl Handle<R=LiveStream>,
    matcher: StreamMatcher<'code>,
    scratch: impl Handle<R=Scratch>,
  ) -> Self {
    Self {
      live: Box::new(live),
      matcher,
      scratch: Box::new(scratch),
    }
  }

  /// Write a single contiguous string into the automaton.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, stream::*, matchers::*};
  ///   use std::ops::Range;
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
  ///   let scratch = db.allocate_scratch()?;
  ///   let live = db.allocate_stream()?;
  ///
  ///   // Create the `matches` vector which is mutably captured in the dyn closure.
  ///   let mut matches: Vec<StreamMatch> = Vec::new();
  ///   // Capture `matches` into `match_fn`;
  ///   // in this case, `match_fn` is an unboxed stack-allocated closure.
  ///   let mut match_fn = |m| {
  ///     matches.push(m);
  ///     MatchResult::Continue
  ///   };
  ///
  ///   {
  ///     // `matcher` now keeps the reference to `matches` alive
  ///     // in rustc's local lifetime tracking.
  ///     let matcher = StreamMatcher::new(&mut match_fn);
  ///     let mut sink = ScratchStreamSink::new(live, matcher, scratch);
  ///
  ///     sink.scan("aadvarka".into())?;
  ///     sink.scan("a".into())?;
  ///     sink.flush_eod()?;
  ///   }
  ///   // `matches` is now "unlocked" by rustc after `matcher` was dropped!
  ///   let matches: Vec<Range<usize>> = matches
  ///     .into_iter()
  ///     .map(|m| m.range.into())
  ///     .collect();
  ///   assert_eq!(&matches, &[0..1, 0..2, 4..5, 7..8, 7..9]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan<'data>(&mut self, data: ByteSlice<'data>) -> Result<(), VectorscanRuntimeError> {
    let Self {
      live,
      matcher,
      scratch,
    } = self;
    scratch
      .make_mut()?
      .scan_sync_stream(live.make_mut()?, matcher, data)
  }

  /// Write vectored string data into the automaton.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, stream::*, matchers::*, sources::*};
  ///   use std::ops::Range;
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
  ///   let scratch = db.allocate_scratch()?;
  ///   let live = db.allocate_stream()?;
  ///
  ///   let input: [ByteSlice; 2] = [
  ///     "aardvarka".into(),
  ///     "asdf".into(),
  ///   ];
  ///
  ///   // Create the `matches` vector which is mutably captured in the dyn closure.
  ///   let mut matches: Vec<StreamMatch> = Vec::new();
  ///   // Capture `matches` into `match_fn`;
  ///   // in this case, `match_fn` is an unboxed stack-allocated closure.
  ///   let mut match_fn = |m| {
  ///     matches.push(m);
  ///     MatchResult::Continue
  ///   };
  ///
  ///   {
  ///     // `matcher` now keeps the reference to `matches` alive
  ///     // in rustc's local lifetime tracking.
  ///     let matcher = StreamMatcher::new(&mut match_fn);
  ///     let mut sink = ScratchStreamSink::new(live, matcher, scratch);
  ///
  ///     sink.scan_vectored(input.as_ref().into())?;
  ///     sink.flush_eod()?;
  ///   }
  ///   // `matches` is now "unlocked" by rustc after `matcher` was dropped!
  ///   let matches: Vec<Range<usize>> = matches
  ///     .into_iter()
  ///     .map(|m| m.range.into())
  ///     .collect();
  ///   assert_eq!(&matches, &[0..1, 0..2, 5..6, 8..9, 8..10]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  #[cfg(feature = "vectored")]
  #[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
  pub fn scan_vectored<'data>(
    &mut self,
    data: VectoredByteSlices<'data, 'data>,
  ) -> Result<(), VectorscanRuntimeError> {
    let Self {
      live,
      matcher,
      scratch,
    } = self;
    scratch
      .make_mut()?
      .scan_sync_vectored_stream(live.make_mut()?, matcher, data)
  }

  /// Trigger any match callbacks that require matching against the end of data
  /// (EOD).
  ///
  /// [`Expression::info()`] returns a [`MatchAtEndBehavior`] can be used to
  /// determine whether this check is necessary. But it typically makes sense
  /// to execute it exactly once at the end of every stream instead of trying
  /// to optimize this away.
  ///
  /// [`Expression::info()`]: crate::expression::Expression::info
  /// [`MatchAtEndBehavior`]: crate::expression::info::MatchAtEndBehavior
  pub fn flush_eod(&mut self) -> Result<(), VectorscanRuntimeError> {
    let Self {
      live,
      matcher,
      scratch,
    } = self;
    scratch
      .make_mut()?
      .flush_eod_sync(live.make_mut()?, matcher)
  }

  /// Reach into [`Self::live`] and call [`LiveStream::reset()`].
  pub fn reset(&mut self) -> Result<(), VectorscanRuntimeError> { self.live.make_mut()?.reset() }
}

pub(crate) mod std_impls {
  use super::ScratchStreamSink;
  #[cfg(feature = "vectored")]
  use crate::sources::vectored::VectoredByteSlices;
  use crate::sources::ByteSlice;

  use std::io;
  #[cfg(feature = "vectored")]
  use std::mem;

  /// A wrapper over [`ScratchStreamSink`] which implements [`io::Write`].
  ///
  /// The reason this is separate from [`ScratchStreamSink`] is that in the case
  /// of vectored writes, [`io::IoSlice`] must be converted into
  /// [`VectoredByteSlices`]. This would typically require a dynamic memory
  /// allocation, but this struct maintains an internal buffer of strings
  /// which is re-used for subsequent vectored writes to avoid repeated dynamic
  /// memory allocation.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, stream::*, matchers::*};
  ///   use std::{ops::Range, io::Write};
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
  ///   let scratch = db.allocate_scratch()?;
  ///   let live = db.allocate_stream()?;
  ///
  ///   let mut matches: Vec<StreamMatch> = Vec::new();
  ///   let mut match_fn = |m| {
  ///     matches.push(m);
  ///     MatchResult::Continue
  ///   };
  ///   // Create a scope to mutably borrow `matches` in via `match_fn`:
  ///   {
  ///     let matcher = StreamMatcher::new(&mut match_fn);
  ///     let sink = ScratchStreamSink::new(live, matcher, scratch);
  ///     let mut sink = StreamWriter::new(sink);
  ///
  ///     sink.write_all(b"aardvark").unwrap();
  ///     // No analogy for tokio's .shutdown(), but we still
  ///     // need to explicitly mark end-of-data:
  ///     sink.inner.flush_eod()?;
  ///   }
  ///   // After `sink` (and therefore `matcher`) was dropped,
  ///   // we can access the closed-over data again!
  ///   let matches: Vec<Range<usize>> = matches
  ///     .into_iter()
  ///     .map(|m| m.range.into())
  ///     .collect();
  ///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub struct StreamWriter<'code> {
    pub inner: ScratchStreamSink<'code>,
    #[cfg(feature = "vectored")]
    vectored_buf_cache: Vec<mem::MaybeUninit<ByteSlice<'static>>>,
  }

  impl<'code> StreamWriter<'code> {
    /// Construct a wrapper over `inner`.
    pub fn new(inner: ScratchStreamSink<'code>) -> Self {
      Self {
        inner,
        #[cfg(feature = "vectored")]
        vectored_buf_cache: Vec::new(),
      }
    }
  }

  impl<'code> io::Write for StreamWriter<'code> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
      self
        .inner
        .scan(ByteSlice::from_slice(buf))
        .map(|()| buf.len())
        .map_err(io::Error::other)
    }

    fn flush(&mut self) -> io::Result<()> { Ok(()) }

    /* TODO: impl `is_write_vectored()` when stabilized! */
    #[cfg(feature = "vectored")]
    #[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> {
      let bufs = VectoredByteSlices::from_io_slices(&mut self.vectored_buf_cache, bufs);
      let len = bufs.length_sum();
      self
        .inner
        .scan_vectored(bufs)
        .map(|()| len)
        .map_err(io::Error::other)
    }
  }
}
pub use std_impls::StreamWriter;

/// Higher-level wrappers for `async` stream parsing.
///
/// # `async` and Stream Parsing
/// As discussed in [Asynchronous String Scanning], `async` code can
/// occasionally offer additional opportunities for parallelism by sending
/// vectorscan matches through an async channel. However, `async` can be
/// particularly useful for stream parsing applications for a different reason:
/// because it uses up much less resources waiting on things like bursty inputs.
/// For example, if you have a pattern with an extremely high match rate, it
/// might be beneficial to buffer its output somewhat instead of performing
/// logic directly in the match callback.
///
/// These structs implement idiomatic `async` interfaces that allow vectorscan
/// to be plugged into a variety of `async` codebases.
///
/// [Asynchronous String Scanning]: crate::state::Scratch#asynchronous-string-scanning
#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
pub mod channel {
  use super::LiveStream;
  #[cfg(feature = "vectored")]
  use crate::sources::vectored::VectoredByteSlices;
  use crate::{
    error::{ScanError, VectorscanRuntimeError},
    matchers::{
      stream::{SendStreamMatcher, StreamMatch},
      MatchResult,
    },
    sources::ByteSlice,
    state::Scratch,
  };

  use futures_core::stream::Stream;
  use handles::Handle;
  use tokio::{sync::mpsc, task};

  use std::mem;

  /// An `async` version of [`super::ScratchStreamSink`].
  ///
  /// By holding handles to [`Self::live`] and [`Self::scratch`], the stream
  /// scanning API can be made quite fluent, without as many parameters per
  /// call:
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> { tokio_test::block_on(async {
  ///   use vectorscan::{expression::*, flags::*, stream::channel::*, matchers::*};
  ///   use futures_util::StreamExt;
  ///   use std::ops::Range;
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
  ///   let scratch = db.allocate_scratch()?;
  ///   let live = db.allocate_stream()?;
  ///
  ///   let mut match_fn = |_: &_| MatchResult::Continue;
  ///   let mut sink = ScratchStreamSinkChannel::new(live, &mut match_fn, scratch);
  ///
  ///   sink.scan("aardvark".into()).await?;
  ///   sink.flush_eod().await?;
  ///
  ///   let matches: Vec<Range<usize>> = sink.collect_matches()
  ///     .map(|m| m.range.into())
  ///     .collect()
  ///     .await;
  ///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
  ///   Ok(())
  /// })}
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub struct ScratchStreamSinkChannel<'code> {
    /// Cloneable handle to a stateful stream.
    pub live: Box<dyn Handle<R=LiveStream>+Send>,
    /// A "handler function" synthesized by [`Self::new()`] which closes over an
    /// [`mpsc::UnboundedSender`].
    pub hf: Box<dyn FnMut(StreamMatch) -> MatchResult+Send+'code>,
    /// Cloneable handle to a scratch space initialized for the same db as
    /// [`Self::live`].
    pub scratch: Box<dyn Handle<R=Scratch>+Send>,
    /// The other half of the sender/receiver pair created by [`Self::new()`].
    pub rx: mpsc::UnboundedReceiver<StreamMatch>,
  }

  impl<'code> ScratchStreamSinkChannel<'code> {
    fn translate_async_sender(
      hf: &'code mut (dyn FnMut(&StreamMatch) -> MatchResult+Send+'code),
      tx: mpsc::UnboundedSender<StreamMatch>,
    ) -> Box<dyn FnMut(StreamMatch) -> MatchResult+Send+'code> {
      Box::new(move |m| {
        let result = hf(&m);
        tx.send(m).unwrap();
        result
      })
    }

    pub fn new(
      live: impl Handle<R=LiveStream>+Send,
      hf: &'code mut (dyn FnMut(&StreamMatch) -> MatchResult+Send+'code),
      scratch: impl Handle<R=Scratch>+Send,
    ) -> Self {
      let (tx, rx) = mpsc::unbounded_channel();
      let hf = Self::translate_async_sender(hf, tx);
      Self {
        live: Box::new(live),
        hf,
        scratch: Box::new(scratch),
        rx,
      }
    }

    pub async fn scan<'data>(&mut self, data: ByteSlice<'data>) -> Result<(), ScanError> {
      /* Make the mutable resources static. */
      let Self {
        live, hf, scratch, ..
      } = self;
      let live: &'static mut LiveStream = unsafe { mem::transmute(live.make_mut()?) };
      let scratch: &'static mut Scratch = unsafe { mem::transmute(scratch.make_mut()?) };
      let data: ByteSlice<'static> = unsafe { mem::transmute(data) };

      /* Generate a vtable pointing to the heap-allocated handler function hf. */
      let hf: &mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code) = hf;
      let matcher = SendStreamMatcher::new(hf);
      let mut matcher: SendStreamMatcher<'static> = unsafe { mem::transmute(matcher) };

      task::spawn_blocking(move || scratch.scan_sync_stream(live, matcher.as_mut_basic(), data))
        .await??;
      Ok(())
    }

    #[cfg(feature = "vectored")]
    #[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
    pub async fn scan_vectored<'data>(
      &mut self,
      data: VectoredByteSlices<'data, 'data>,
    ) -> Result<(), ScanError> {
      /* Make the mutable resources static. */
      let Self {
        live, hf, scratch, ..
      } = self;
      let live: &'static mut LiveStream = unsafe { mem::transmute(live.make_mut()?) };
      let scratch: &'static mut Scratch = unsafe { mem::transmute(scratch.make_mut()?) };
      let data: VectoredByteSlices<'static, 'static> = unsafe { mem::transmute(data) };

      /* Generate a vtable pointing to the heap-allocated handler function hf. */
      let hf: &mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code) = hf;
      let matcher = SendStreamMatcher::new(hf);
      let mut matcher: SendStreamMatcher<'static> = unsafe { mem::transmute(matcher) };

      task::spawn_blocking(move || {
        scratch.scan_sync_vectored_stream(live, matcher.as_mut_basic(), data)
      })
      .await??;
      Ok(())
    }

    pub async fn flush_eod(&mut self) -> Result<(), ScanError> {
      /* Make the mutable resources static. */
      let Self {
        live, hf, scratch, ..
      } = self;
      let live: &'static mut LiveStream = unsafe { mem::transmute(live.make_mut()?) };
      let scratch: &'static mut Scratch = unsafe { mem::transmute(scratch.make_mut()?) };

      /* Generate a vtable pointing to the heap-allocated handler function hf. */
      let hf: &mut (dyn FnMut(StreamMatch) -> MatchResult+Send+'code) = hf;
      let matcher = SendStreamMatcher::new(hf);
      let mut matcher: SendStreamMatcher<'static> = unsafe { mem::transmute(matcher) };

      task::spawn_blocking(move || {
        scratch.flush_eod_sync(live.make_mut()?, matcher.as_mut_basic())
      })
      .await??;
      Ok(())
    }

    pub fn collect_matches(mut self) -> impl Stream<Item=StreamMatch> {
      self.rx.close();
      crate::async_utils::UnboundedReceiverStream(self.rx)
    }

    pub fn reset(&mut self) -> Result<(), VectorscanRuntimeError> { self.live.make_mut()?.reset() }
  }

  #[cfg(feature = "tokio-impls")]
  pub(crate) mod tokio_impls {
    use super::ScratchStreamSinkChannel;
    #[cfg(feature = "vectored")]
    use crate::sources::vectored::VectoredByteSlices;
    use crate::sources::ByteSlice;

    use futures_util::TryFutureExt;
    use tokio::io;

    #[cfg(feature = "vectored")]
    use std::io::IoSlice;
    use std::{
      future::Future,
      mem,
      pin::Pin,
      task::{ready, Context, Poll},
    };

    ///```
    /// #[cfg(feature = "compiler")]
    /// fn main() -> Result<(), vectorscan::error::VectorscanError> { tokio_test::block_on(async {
    ///   use vectorscan::{expression::*, flags::*, stream::channel::*, matchers::*};
    ///   use futures_util::StreamExt;
    ///   use tokio::io::AsyncWriteExt;
    ///   use std::ops::Range;
    ///
    ///   let expr: Expression = "a+".parse()?;
    ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_LARGE)?;
    ///   let scratch = db.allocate_scratch()?;
    ///   let live = db.allocate_stream()?;
    ///
    ///   let mut match_fn = |_: &_| MatchResult::Continue;
    ///   let sink = ScratchStreamSinkChannel::new(live, &mut match_fn, scratch);
    ///   let mut sink = AsyncStreamWriter::new(sink);
    ///
    ///   sink.write_all(b"aardvark").await.unwrap();
    ///   sink.shutdown().await.unwrap();
    ///
    ///   let matches: Vec<Range<usize>> = sink.inner.collect_matches()
    ///     .map(|m| m.range.into())
    ///     .collect()
    ///     .await;
    ///   assert_eq!(&matches, &[0..1, 0..2, 5..6]);
    ///   Ok(())
    /// })}
    /// # #[cfg(not(feature = "compiler"))]
    /// # fn main() {}
    /// ```
    pub struct AsyncStreamWriter<'code> {
      pub inner: ScratchStreamSinkChannel<'code>,
      #[cfg(feature = "vectored")]
      vectored_buf_cache: Vec<mem::MaybeUninit<ByteSlice<'static>>>,
      write_future: Option<Pin<Box<dyn Future<Output=io::Result<usize>>+'code>>>,
      shutdown_future: Option<Pin<Box<dyn Future<Output=io::Result<()>>+'code>>>,
    }

    impl<'code> AsyncStreamWriter<'code> {
      pub fn new(inner: ScratchStreamSinkChannel<'code>) -> Self {
        Self {
          inner,
          #[cfg(feature = "vectored")]
          vectored_buf_cache: Vec::new(),
          write_future: None,
          shutdown_future: None,
        }
      }
    }

    unsafe impl<'code> Send for AsyncStreamWriter<'code> {}

    impl<'code> io::AsyncWrite for AsyncStreamWriter<'code> {
      fn poll_write(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
      ) -> Poll<io::Result<usize>> {
        if self.write_future.is_some() {
          let ret = ready!(self
            .as_mut()
            .write_future
            .as_mut()
            .unwrap()
            .as_mut()
            .poll(cx));

          self.write_future = None;

          Poll::Ready(ret)
        } else {
          let mut fut: Pin<Box<dyn Future<Output=io::Result<usize>>+'code>> = {
            let s: &'code mut Self = unsafe { mem::transmute(self.as_mut().get_mut()) };
            let buf: &'code [u8] = unsafe { mem::transmute(buf) };
            let buf_len = buf.len();
            let buf = ByteSlice::from_slice(buf);
            Box::pin(
              s.inner
                .scan(buf)
                .map_ok(move |()| buf_len)
                .map_err(io::Error::other),
            )
          };

          if let Poll::Ready(ret) = fut.as_mut().poll(cx) {
            return Poll::Ready(ret);
          }

          self.write_future = Some(fut);

          Poll::Pending
        }
      }

      fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
      }

      fn poll_shutdown(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        if self.shutdown_future.is_some() {
          let ret = ready!(self
            .as_mut()
            .shutdown_future
            .as_mut()
            .unwrap()
            .as_mut()
            .poll(cx));

          self.shutdown_future = None;

          Poll::Ready(ret)
        } else {
          let mut fut: Pin<Box<dyn Future<Output=io::Result<()>>+'code>> = {
            let s: &'code mut Self = unsafe { mem::transmute(self.as_mut().get_mut()) };
            Box::pin(s.inner.flush_eod().map_err(io::Error::other))
          };

          if let Poll::Ready(ret) = fut.as_mut().poll(cx) {
            return Poll::Ready(ret);
          }

          self.shutdown_future = Some(fut);

          Poll::Pending
        }
      }

      #[cfg(feature = "vectored")]
      #[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
      fn is_write_vectored(&self) -> bool { true }

      #[cfg(feature = "vectored")]
      #[cfg_attr(docsrs, doc(cfg(feature = "vectored")))]
      fn poll_write_vectored(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        bufs: &[IoSlice<'_>],
      ) -> Poll<io::Result<usize>> {
        if self.write_future.is_some() {
          let ret = ready!(self
            .as_mut()
            .write_future
            .as_mut()
            .unwrap()
            .as_mut()
            .poll(cx));

          self.write_future = None;

          Poll::Ready(ret)
        } else {
          let mut fut: Pin<Box<dyn Future<Output=io::Result<usize>>+'code>> = {
            let s: &'code mut Self = unsafe { mem::transmute(self.as_mut().get_mut()) };
            let bufs: &'code [IoSlice<'code>] = unsafe { mem::transmute(bufs) };
            let bufs = VectoredByteSlices::from_io_slices(&mut s.vectored_buf_cache, bufs);
            let len = bufs.length_sum();
            Box::pin(
              s.inner
                .scan_vectored(bufs)
                .map_ok(move |()| len)
                .map_err(io::Error::other),
            )
          };

          if let Poll::Ready(ret) = fut.as_mut().poll(cx) {
            return Poll::Ready(ret);
          }

          self.write_future = Some(fut);

          Poll::Pending
        }
      }
    }
  }
  #[cfg(feature = "tokio-impls")]
  #[cfg_attr(docsrs, doc(cfg(feature = "tokio-impls")))]
  pub use tokio_impls::AsyncStreamWriter;
}

pub mod compress {
  use super::{LiveStream, NativeStream};
  use crate::{
    database::Database,
    error::{CompressionError, VectorscanRuntimeError},
    hs,
  };

  use std::{mem, ptr};

  pub enum CompressReserveBehavior {
    NewBuf,
    ExpandBuf(Vec<u8>),
    FixedSizeBuf(Vec<u8>),
  }

  impl CompressReserveBehavior {
    pub fn current_buf(&mut self) -> Option<&mut Vec<u8>> {
      match self {
        Self::NewBuf => None,
        Self::ExpandBuf(ref mut buf) => Some(buf),
        Self::FixedSizeBuf(ref mut buf) => Some(buf),
      }
    }
  }

  enum ReserveResponse {
    MadeSpace(Vec<u8>),
    NoSpace(Vec<u8>),
  }

  impl CompressReserveBehavior {
    fn reserve(self, n: usize) -> ReserveResponse {
      match self {
        Self::NewBuf => ReserveResponse::MadeSpace(Vec::with_capacity(n)),
        Self::ExpandBuf(mut buf) => {
          if n > buf.capacity() {
            let additional = n - buf.capacity();
            buf.reserve(additional);
          }
          ReserveResponse::MadeSpace(buf)
        },
        Self::FixedSizeBuf(buf) => {
          if buf.capacity() <= n {
            ReserveResponse::NoSpace(buf)
          } else {
            ReserveResponse::MadeSpace(buf)
          }
        },
      }
    }
  }

  pub struct CompressedStream {
    pub buf: Vec<u8>,
  }

  impl CompressedStream {
    pub fn compress(
      mut into: CompressReserveBehavior,
      live: &LiveStream,
    ) -> Result<Self, CompressionError> {
      let mut required_space: usize = 0;

      /* If we already have an existing buffer to play around with, try that right
       * off to see if it was enough to avoid further allocations. */
      if let Some(ref mut buf) = into.current_buf() {
        match VectorscanRuntimeError::from_native(unsafe {
          hs::hs_compress_stream(
            live.as_ref_native(),
            mem::transmute(buf.as_mut_ptr()),
            buf.capacity(),
            &mut required_space,
          )
        }) {
          Err(VectorscanRuntimeError::InsufficientSpace) => (),
          Err(e) => return Err(e.into()),
          Ok(()) => {
            debug_assert!(buf.capacity() >= required_space);
            unsafe {
              buf.set_len(required_space);
            }
            return Ok(Self {
              buf: mem::take(buf),
            });
          },
        }
      } else {
        /* Otherwise (e.g. if we have a NewBuf), get the required space first
         * before trying to allocate anything by providing
         * NULL for the data pointer. */
        assert_eq!(
          Err(VectorscanRuntimeError::InsufficientSpace),
          VectorscanRuntimeError::from_native(unsafe {
            hs::hs_compress_stream(
              live.as_ref_native(),
              ptr::null_mut(),
              0,
              &mut required_space,
            )
          })
        );
      }
      /* At this point, we know some allocation is necessary, and the
       * `required_space` variable is populated with the amount of space
       * necessary to compress. */

      /* Allocate or fail allocation. */
      let buf = match into.reserve(required_space) {
        ReserveResponse::NoSpace(buf) => {
          /* This is supposed to be what ReserveResponse checks. */
          debug_assert!(required_space > buf.len());
          return Err(CompressionError::NoSpace(required_space, buf));
        },
        ReserveResponse::MadeSpace(mut buf) => {
          let mut allocated_space: usize = 0;
          VectorscanRuntimeError::from_native(unsafe {
            hs::hs_compress_stream(
              live.as_ref_native(),
              mem::transmute(buf.as_mut_ptr()),
              buf.capacity(),
              &mut allocated_space,
            )
          })?;
          /* No particular reason these values should be different across two
           * subsequent calls. */
          debug_assert_eq!(required_space, allocated_space);
          debug_assert!(allocated_space <= buf.capacity());
          unsafe {
            buf.set_len(allocated_space);
          }
          buf
        },
      };

      Ok(Self { buf })
    }

    pub fn expand(&self, db: &Database) -> Result<LiveStream, VectorscanRuntimeError> {
      let mut inner = ptr::null_mut();
      VectorscanRuntimeError::from_native(unsafe {
        hs::hs_expand_stream(
          db.as_ref_native(),
          &mut inner,
          mem::transmute(self.buf.as_ptr()),
          self.buf.len(),
        )
      })?;
      Ok(unsafe { LiveStream::from_native(inner) })
    }

    /// # Safety
    /// `self` and `to` must have been opened against the same db!
    pub unsafe fn expand_into(&self, to: &mut LiveStream) -> Result<(), VectorscanRuntimeError> {
      VectorscanRuntimeError::from_native(hs::hs_direct_expand_into(
        to.as_mut_native(),
        mem::transmute(self.buf.as_ptr()),
        self.buf.len(),
      ))
    }

    /// # Safety
    /// `to` must point to an allocation of at least [`Database::stream_size()`]
    /// bytes in size given `db`!
    pub unsafe fn expand_into_at(
      &self,
      db: &Database,
      to: *mut NativeStream,
    ) -> Result<(), VectorscanRuntimeError> {
      VectorscanRuntimeError::from_native(hs::hs_expand_stream_at(
        db.as_ref_native(),
        mem::transmute(self.buf.as_ptr()),
        self.buf.len(),
        to,
      ))
    }
  }
}

/* ///``` */
/* /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
 * tokio_test::block_on(async { */
/* /// use vectorscan::{expression::*, matchers::*, flags::*, stream::*,
 * error::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// */
/* /// let expr: Expression = "a+".parse()?; */
/* /// let db = expr.compile(Flags::UTF8, Mode::STREAM)?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// struct S(usize); */
/* /// impl StreamScanner for S { */
/* ///   fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult { */
/* ///     if self.0 < 2 { self.0 += 1; MatchResult::Continue } else {
 * MatchResult::CeaseMatching } */
/* ///   } */
/* ///   fn new() -> Self where Self: Sized { Self(0) } */
/* ///   fn reset(&mut self) { self.0 = 0; } */
/* ///   fn boxed_clone(&self) -> Box<dyn StreamScanner> {
 * Box::new(Self(self.0)) } */
/* /// } */
/* /// */
/* /// let mut s = Streamer::open::<S>(&db, scratch.into())?; */
/* /// */
/* /// let msg = "aardvark"; */
/* /// if let Err(e) = s.write_all(msg.as_bytes()).await { */
/* ///   let e = *e.into_inner().unwrap().downcast::<ScanError>().unwrap(); */
/* ///   if let ScanError::ReturnValue(ref e) = e { */
/* ///     assert_eq!(*e, VectorscanRuntimeError::ScanTerminated); */
/* ///   } else { unreachable!(); }; */
/* /// } else { unreachable!(); } */
/* /// s.shutdown().await.unwrap(); */
/* /// let rx = s.stream_results(); */
/* /// */
/* /// let results: Vec<&str> = rx.map(|StreamMatch { range, .. }|
 * &msg[range]).collect().await; */
/* /// // NB: results have no third "aardva" result because of the early
 * CeaseMatching! */
/* /// assert_eq!(results, vec!["a", "aa"]); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub struct Streamer { */
/* pub sink: StreamSink, */
/* pub rx: mpsc::UnboundedReceiver<StreamMatch>, */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
 * tokio_test::block_on(async { */
/* /// use vectorscan::{expression::*, flags::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// */
/* /// let expr: Expression = "a+".parse()?; */
/* /// let db = expr.compile( */
/* ///   Flags::UTF8 | Flags::SOM_LEFTMOST, */
/* ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* /// )?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// let s1 = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */
/* /// */
/* /// let compressed = s1.compress(CompressReserveBehavior::NewBuf)?; */
/* /// std::mem::drop(s1); */
/* /// */
/* /// let msg = "aardvark"; */
/* /// let mut s2 = compressed.expand(&db)?; */
/* /// s2.scan(msg.as_bytes().into()).await?; */
/* /// s2.flush_eod().await?; */
/* /// let rx = s2.stream_results(); */
/* /// */
/* /// let results: Vec<&str> = rx */
/* ///   .map(|StreamMatch { range, .. }| &msg[range]) */
/* ///   .collect() */
/* ///   .await; */
/* /// assert_eq!(results, vec!["a", "aa", "a"]); */
/* /// # Ok(()) */
/* /// # })} */
/* pub fn compress( */
/* &self, */
/* into: CompressReserveBehavior, */
/* ) -> Result<CompressedStream, CompressionError> { */
/* self.sink.compress(into) */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
 * tokio_test::block_on(async { */
/* /// use vectorscan::{expression::*, matchers::*, flags::*, stream::*,
 * error::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// */
/* /// let expr: Literal = "asdf".parse()?; */
/* /// let db = expr.compile(Flags::default(), Mode::STREAM)?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// struct S(usize); */
/* /// impl StreamScanner for S { */
/* ///   fn stream_scan(&mut self, _m: &StreamMatch) -> MatchResult { */
/* ///     if self.0 < 2 { self.0 += 1; MatchResult::Continue } else {
 * MatchResult::CeaseMatching } */
/* ///   } */
/* ///   fn new() -> Self where Self: Sized { Self(0) } */
/* ///   fn reset(&mut self) { self.0 = 0; } */
/* ///   fn boxed_clone(&self) -> Box<dyn StreamScanner> {
 * Box::new(Self(self.0)) } */
/* /// } */
/* /// */
/* /// let mut s1 = Streamer::open::<S>(&db, scratch.into())?; */
/* /// */
/* /// s1.write_all(b"asdf").await.unwrap(); */
/* /// let mut s2 = s1.try_clone()?; */
/* /// s1.shutdown().await.unwrap(); */
/* /// let rx1 = s1.stream_results(); */
/* /// s2.write_all(b"asdf").await.unwrap(); */
/* /// s2.reset_no_flush()?; */
/* /// let rx2 = s2.reset_channel(); */
/* /// if let Err(e) = s2.write_all(b"asdfasdfasdf").await { */
/* ///   let e = *e.into_inner().unwrap().downcast::<ScanError>().unwrap(); */
/* ///   if let ScanError::ReturnValue(ref e) = e { */
/* ///     assert_eq!(*e, VectorscanRuntimeError::ScanTerminated); */
/* ///   } else { unreachable!(); } */
/* /// } else { unreachable!(); } */
/* /// s2.shutdown().await.unwrap(); */
/* /// let rx3 = s2.stream_results(); */
/* /// */
/* /// let m1: Vec<_> = rx1.collect().await; */
/* /// let m2: Vec<_> = rx2.collect().await; */
/* /// let m3: Vec<_> = rx3.collect().await; */
/* /// assert_eq!(1, m1.len()); */
/* /// assert_eq!(1, m2.len()); */
/* /// assert_eq!(2, m3.len()); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* /// */
/* /// **TODO: docs** */
/* /// */
/* ///``` */
/* /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
 * tokio_test::block_on(async { */
/* /// use vectorscan::{expression::*, flags::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// */
/* /// let expr: Expression = "asdf$".parse()?; */
/* /// let db = expr.compile(Flags::UTF8, Mode::STREAM)?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// let mut s = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */
/* /// */
/* /// s.write_all(b"asdf").await.unwrap(); */
/* /// s.reset_flush().await?; */
/* /// let rx = s.reset_channel(); */
/* /// s.write_all(b"asdf").await.unwrap(); */
/* /// s.reset_no_flush()?; */
/* /// let rx2 = s.reset_channel(); */
/* /// s.write_all(b"asdf").await.unwrap(); */
/* /// s.shutdown().await.unwrap(); */
/* /// let rx3 = s.stream_results(); */
/* /// */
/* /// let m1: Vec<_> = rx.collect().await; */
/* /// let m2: Vec<_> = rx2.collect().await; */
/* /// let m3: Vec<_> = rx3.collect().await; */
/* /// assert!(!m1.is_empty()); */
/* /// // This will be empty, because .reset_no_flush() was called on sink2 */
/* /// // and the pattern "asdf$" requires matching against the end of data: */
/* /// assert!(m2.is_empty()); */
/* /// assert!(!m3.is_empty()); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub fn reset_no_flush(&mut self) -> Result<(), VectorscanRuntimeError> { */
/* self.sink.reset_no_flush() */
/* } */

/* ///``` */
/* /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
 * tokio_test::block_on(async { */
/* /// use vectorscan::{expression::*, flags::*, stream::*}; */
/* /// use futures_util::StreamExt; */
/* /// use tokio::io::AsyncWriteExt; */
/* /// use std::ops; */
/* /// */
/* /// let expr: Literal = "asdf".parse()?; */
/* /// let db = expr.compile( */
/* ///   Flags::SOM_LEFTMOST, */
/* ///   Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* /// )?; */
/* /// let scratch = db.allocate_scratch()?; */
/* /// */
/* /// let mut s = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */
/* /// */
/* /// s.write_all(b"asdf..").await.unwrap(); */
/* /// let rx = s.reset_channel(); */
/* /// s.reset_flush().await?; */
/* /// s.write_all(b"..asdf").await.unwrap(); */
/* /// s.shutdown().await.unwrap(); */
/* /// let rx2 = s.stream_results(); */
/* /// */
/* /// let m1: Vec<ops::Range<usize>> = rx.map(|m| m.range).collect().await; */
/* /// let m2: Vec<ops::Range<usize>> = rx2.map(|m| m.range).collect().await; */
/* /// // The stream state should have been reset, so rx2 should have
 * restarted the stream offset */
/* /// // from the beginning: */
/* /// assert_eq!(m1, vec![0..4]); */
/* /// assert_eq!(m2, vec![2..6]); */
/* /// # Ok(()) */
/* /// # })} */
/* /// ``` */
/* pub async fn reset_flush(&mut self) -> Result<(), ScanError> {
 * self.sink.reset_flush().await } */

/* } */

/* #[cfg(all(test, feature = "compiler"))] */
/* mod test { */
/* use super::*; */
/* use crate::{ */
/* expression::Expression, */
/* flags::{Flags, Mode}, */
/* }; */

/* use futures_util::StreamExt; */

/* use std::{mem, sync::Arc}; */

/* #[tokio::test] */
/* async fn clone_scratch() -> Result<(), eyre::Report> { */
/* let expr: Expression = "asdf$".parse()?; */
/* let db = expr.compile(Flags::UTF8, Mode::STREAM)?; */

/* let live = LiveStream::open(&db)?; */

/* let scratch = Arc::new(db.allocate_scratch()?; */
/* let s2 = Arc::clone(&scratch); */

/* let msg = "asdf"; */
/* let mut s = StreamSinkChannel::new::<TrivialScanner>(&db, s2)?; */
/* mem::drop(scratch); */
/* s.scan(msg.into()).await?; */
/* s.flush_eod().await?; */
/* let rx = s.stream_results(); */

/* let results: Vec<&str> = rx.map(|m| &msg[m.range]).collect().await; */
/* assert_eq!(&results, &["asdf"]); */
/* Ok(()) */
/* } */

/* #[tokio::test] */
/* async fn compress() -> Result<(), eyre::Report> { */
/* let expr: Expression = "a+".parse()?; */
/* let db = expr.compile( */
/* Flags::UTF8 | Flags::SOM_LEFTMOST, */
/* Mode::STREAM | Mode::SOM_HORIZON_LARGE, */
/* )?; */
/* let scratch = db.allocate_scratch()?; */

/* let s1 = Streamer::open::<TrivialScanner>(&db, scratch.into())?; */

/* let compressed = s1.compress(CompressReserveBehavior::NewBuf)?; */
/* mem::drop(s1); */

/* let msg = "aardvark"; */
/* let mut s2 = compressed.expand(&db)?; */
/* s2.scan(msg.as_bytes().into()).await?; */
/* s2.flush_eod().await?; */
/* let rx = s2.stream_results(); */

/* let results: Vec<&str> = rx */
/* .map(|StreamMatch { range, .. }| &msg[range]) */
/* .collect() */
/* .await; */
/* assert_eq!(results, vec!["a", "aa", "a"]); */
/* Ok(()) */
/* } */
/* } */

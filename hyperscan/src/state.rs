/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Allocate and initialize mutable [scratch space] required for string
//! searching.
//!
//! [scratch space]: https://intel.github.io/hyperscan/dev-reference/runtime.html#scratch-space
//!
//! # Mutable State and String Searching
//! While other regex libraries such as [`re2`](https://docs.rs/re2) and [`regex`](https://docs.rs/regex) may also
//! internally make use of mutable state e.g. for a lazy DFA, they typically do
//! not expose this to the user, in order to simplify the search interface.
//! However, this often requires the regex library to juggle complicated
//! heuristics, implement atomic locking protocols, and/or pre-allocate a
//! multi-layer internal cache to improve performance in multi-threaded
//! programs: see a [failed attempt from the author to implement a lock-free
//! stack to manage these internal caches in the `regex` library](https://github.com/rust-lang/regex/issues/934#issuecomment-1703299897).
//!
//! ## Manual Cache Management
//! The `re2` library goes above and beyond to avoid handing this thorny problem
//! down to its users, implementing a re-entrant protocol for accessing the
//! stateful lazy DFA from multiple threads.`[FIXME: citation needed]` This is
//! impressive partially because it is considered so complex that `hyperscan`
//! and `regex` don't plan to implement this approach at all.`[FIXME: citation
//! needed]` **A performant implementation of a lock-free lazy DFA (or a data
//! structure to help in implementing such a DFA) might
//! therefore be a useful contribution to the field of regex engines.`[FIXME:
//! citation needed]`**
//!
//! However, mechanisms like this to hide mutable state from the user often end
//! up resorting to complex heuristics and multi-layer caches in order to cover
//! all possible performance scenarios. One alternative which avoids the need to
//! implement these complex heuristics is to instead just expose the mutable
//! state to the user, since the end user is often the most
//! knowledgeable about their code's performance characteristics anyway.`[no
//! citation needed]` Indeed, the `regex` crate exposes precisely this
//! functionality via the separate lower-level `regex-automata` crate through
//! methods such as [`meta::Regex::search_with()`](https://docs.rs/regex-automata/latest/regex_automata/meta/struct.Regex.html#method.search_with).
//! **The hyperscan library takes this (re-)inversion of control to the extreme
//! in requiring the user to provide exclusive mutable access to a previously
//! initialized scratch space for every search (see [Setup
//! Methods](Scratch#setup-methods)).**
//!
//! ### Atypical Search Interface
//! Because this scratch space represents the only mutable state involved in a
//! search, this crate has chosen to make the [`Scratch`] type the main entry
//! point to hyperscan's [search methods](Scratch#synchronous-string-scanning).
//! Because a single scratch space can be initialized for multiple dbs, the
//! immutable [`Database`] type is provided as a parameter. This is contrary to
//! most other regex engines such as `regex` and `re2`, where the compiled regex
//! itself is typically used as the `&self` parameter to most search methods.
//!
//! ## Handling Cache Contention in Rust
//! While the hyperscan native library must expose a simple C ABI, Rust offers a
//! much richer library of tools for sharing and explicitly cloning state in
//! order to mutate it. **Indeed, safe Rust code should never experience scratch
//! space contention.** While the hyperscan library performs a best-effort
//! attempt to identify scratch space contention and error out with
//! [`HyperscanRuntimeError::ScratchInUse`], a user of this crate should never
//! see that error from safe Rust code.
//!
//! ### Minimizing Scratch Contention
//! Unfortunately (or perhaps fortunately), the way safe Rust avoids scratch
//! space contention is by simply refusing to compile code with multiple mutable
//! references to the same value. This library provides the
//! [`Database::allocate_scratch()`] convenience method to encourage the
//! allocation of 1 scratch space per database, so that searching against
//! separate databases doesn't introduce contention.
//!
//! However, there remain several use cases that require multiple separate
//! mutable scratch spaces to be available at the same time. **In particular,
//! invoking hyperscan recursively (inside a match callback) always requires
//! exclusive mutable access to multiple distinct scratch allocations at once.**
//! While recursive searches are supported by the hyperscan library, the
//! creative use of [`ExpressionSet`](crate::expression::ExpressionSet) with
//! [`Flags::COMBINATION`](crate::flags::Flags::COMBINATION) and/or
//! [`ExprExt`](crate::expression::ExprExt) configuration may be able to express
//! some types of search logic without requiring a recursive search or other
//! extensive logic in the match callback.
//!
//! ### Copy-on-Write
//! [`Scratch`] implements [`Clone`] via [`Scratch::try_clone()`] so that its
//! contents may be copied on demand. This can be leveraged by smart pointer
//! types to implement [copy-on-write (CoW) semantics](https://en.wikipedia.org/wiki/Copy-on-write)
//! in single and multi-threaded regimes. Some specialized use cases that may
//! benefit from CoW semantics include:
//! - **minimizing allocations for complex search invocations:** Recursive
//!   hyperscan searches are commonly used to implement a form of capturing
//!   groups (although see [`chimera`] for complete PCRE support, including
//!   capture groups). It often makes sense to share the scratch space used for
//!   inner searches, but the same scratch cannot be used for the inner search
//!   while the outer one is still ongoing.
//! - **shallow cloning for async stream combinator APIs:** `async` interfaces
//!   in Rust typically do no work until polled (see
//!   [`Future::poll()`](std::future::Future::poll) or
//!   [`AsyncWrite::poll_write()`](tokio::io::AsyncWrite::poll_write)), so when
//!   writing adapters or combinators we often want to hold a shallow reference
//!   that we can lazily invoke later, to set up any state but only if we
//!   actually receive input.
//! - **centralized registries:** in order to provide an API like `re2` or
//!   `regex` which hides mutable state management from the end user, or to
//!   implement something like regex compile caching for a high-level dynamic
//!   language, we may want to reuse allocations from a shared memory pool.
//!
//! Using CoW semantics with [`Clone`]-able references may also be more
//! performant in some cases than pre-allocating blank new scratch spaces,
//! because the CoW process preserves all previous modifications made to the
//! scratch space when cloning into a new allocation. This produces a sort of
//! abstract conceptual trie in memory, where all later clones of the scratch
//! space retain all the progress from parent clones. **FIXME: BENCHMARK THIS!**
//!
//! #### Synchronous
//! In synchronous, single-threaded code, scratch space contention
//! can only ever occur if another hyperscan search is invoked from within a
//! match callback. Safe Rust will avoid any runtime contention, but it will
//! refuse to compile unless a distinct mutable scratch space is allocated
//! for the recursive search within the match callback. While the scratch space
//! can also just be cloned ahead of time,
//! [`Rc::make_mut()`](std::rc::Rc::make_mut) offers a method to lazily clone
//! scratch allocations only when needed:
//!
//!```
//! #[cfg(feature = "compiler")]
//! fn main() -> Result<(), hyperscan::error::HyperscanError> {
//!   use hyperscan::{expression::*, flags::*, matchers::*, state::*, error::*, sources::*};
//!   use std::rc::Rc;
//!
//!   let ab_expr: Expression = "a.*b".parse()?;
//!   let ab_db = ab_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
//!   let cd_expr: Expression = "cd".parse()?;
//!   let cd_db = cd_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
//!
//!   let mut scratch = Scratch::blank();
//!   scratch.setup_for_db(&ab_db)?;
//!   scratch.setup_for_db(&cd_db)?;
//!
//!   // Compose the "a.*b" and "cd" searches to form an "a(cd)b" matcher.
//!   let msg = "acdb";
//!   // Record the whole match and the (cd) group.
//!   let mut matches: Vec<(&str, &str)> = Vec::new();
//!
//!   // Broken example to trigger ScratchInUse.
//!   let s: *mut Scratch = &mut scratch;
//!   // Use unsafe code to get multiple mutable references to the same allocation:
//!   unsafe { &mut *s }
//!     .scan_sync(&ab_db, msg.into(), |m| {
//!       // Hyperscan was able to detect this contention!
//!       // But this is described as an unreliable best-effort runtime check.
//!       assert_eq!(
//!         unsafe { &mut *s }.scan_sync(&cd_db, m.source, |_| MatchResult::Continue),
//!         Err(HyperscanRuntimeError::ScratchInUse),
//!       );
//!       MatchResult::Continue
//!     })?;
//!
//!   // Try again using Rc::make_mut() to avoid contention:
//!   let mut scratch = Rc::new(scratch);
//!   // This is a shallow copy pointing to the same memory:
//!   let mut scratch2 = scratch.clone();
//!   // Currently, these point to the same allocation:
//!   assert_eq!(
//!     scratch.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!     scratch2.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!   );
//!   // When Rc::make_mut() is first called within the match callback,
//!   // `scratch2` will call Scratch::try_clone() to generate
//!   // a new heap allocation, which `scratch2` then becomes the exclusive owner of.
//!
//!   Rc::make_mut(&mut scratch)
//!     // First search for "a.*b":
//!     .scan_sync(&ab_db, msg.into(), |outer_match| {
//!       // Strip the "^a" and "b$" in order to perform a search of the ".*":
//!       let inner_group: ByteSlice = unsafe { outer_match.source.as_str() }
//!         .strip_prefix('a').unwrap()
//!         .strip_suffix('b').unwrap()
//!         .into();
//!       // Perform the inner search, cloning the scratch space upon first use:
//!       if let Some(m) = Rc::make_mut(&mut scratch2)
//!         // Now search for "cd" within the text matching ".*" from the original pattern:
//!         .full_match(&cd_db, inner_group).unwrap() {
//!         // Record the outer and inner match text:
//!         matches.push(unsafe { (outer_match.source.as_str(), m.source.as_str()) });
//!       }
//!       MatchResult::Continue
//!     })?;
//!
//!   // At least one match was found, so we know the inner matcher was invoked,
//!   // and that the lazy clone has occurred.
//!   assert!(!matches.is_empty());
//!   // After the CoW process, `scratch` and `scratch2` have diverged.
//!   assert_ne!(
//!     scratch.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!     scratch2.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!   );
//!   assert_eq!(&matches, &[("acdb", "cd")]);
//!   Ok(())
//! }
//! # #[cfg(not(feature = "compiler"))]
//! # fn main() {}
//! ```
//!
//! #### Asynchronous
//! In multi-threaded and/or asynchronous safe Rust code, scratch space
//! contention should *still* only ever occur if another hyperscan search is
//! invoked from within a match callback, because Rust exclusive ownership rules
//! can *only* be broken by unsafe code, never by the use of `async` or
//! threading. As a result, the concerns about contention are very similar to
//! the [synchronous](#synchronous) use case.
//!
//! ##### Parallelism Makes Copy-on-Write More Useful
//! However, async code often finds more reasons to make use of copy-on-write.
//!
//! The [Asynchronous String Scanning
//! API](Scratch#asynchronous-string-scanning) is explicitly engineered to
//! decouple match processing from the synchronously-invoked match callback in
//! order to maximize search performance, but that only addresses contention
//! over the synchronously-invoked match callback. **A separate, uncontended
//! scratch space is still necessary in order to perform any recursive hyperscan
//! search on the results of a match in async code, especially if the matches
//! are being processed in parallel with the search.**
//!
//! Where a [`Send`] reference is necessary,
//! [`Arc::make_mut()`](std::sync::Arc) can be used over `Rc` as it uses atomic
//! operations to correctly track ownership of objects shared across threads:
//!
//!```
//! #[cfg(all(feature = "compiler", feature = "async"))]
//! fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
//!   use hyperscan::{expression::*, flags::*, matchers::*, state::*, sources::*};
//!   use futures_util::TryStreamExt;
//!   use std::sync::Arc;
//!
//!   let ab_expr: Expression = "a.*b".parse()?;
//!   let ab_db = ab_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
//!   let cd_expr: Expression = "cd".parse()?;
//!   let cd_db = cd_expr.compile(Flags::default(), Mode::BLOCK)?;
//!
//!   let mut scratch = Scratch::blank();
//!   scratch.setup_for_db(&ab_db)?;
//!   scratch.setup_for_db(&cd_db)?;
//!
//!   let msg = "acdb";
//!
//!   // Use Arc::make_mut() to lazily clone.
//!   let mut scratch = Arc::new(scratch);
//!   // This will only call the underlying Scratch::try_clone()
//!   // if the outer scan matches and Arc::make_mut() is called:
//!   let mut scratch2 = scratch.clone();
//!   // Currently, these point to the same allocation:
//!   assert_eq!(
//!     scratch.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!     scratch2.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!   );
//!
//!   let matches: Vec<(&str, &str)> = Arc::make_mut(&mut scratch)
//!     // Match "a.*b":
//!     .scan_channel(&ab_db, msg.into(), |_| MatchResult::Continue)
//!     .map_ok(|outer_match| {
//!       // Strip the "^a" and "b$" in order to perform a search of the ".*":
//!       let inner_group: ByteSlice = unsafe { outer_match.source.as_str() }
//!         .strip_prefix('a').unwrap()
//!         .strip_suffix('b').unwrap()
//!         .into();
//!       // This callback runs in parallel with the .scan_channel() task,
//!       // so it needs its own exclusive mutable access:
//!       Arc::make_mut(&mut scratch2)
//!         // Perform another scan on the contents of the match:
//!         .scan_channel(&cd_db, inner_group, |_| MatchResult::Continue)
//!         // Return both inner and outer match objects:
//!         .map_ok(move |captured_match| (outer_match, captured_match))
//!     })
//!     // Our .map_ok() method itself returns a stream, so flatten them out:
//!     .try_flatten()
//!     // Extract match text from match objects:
//!     .map_ok(|(outer_match, captured_match)| unsafe { (
//!       outer_match.source.as_str(),
//!       captured_match.source.as_str(),
//!      ) })
//!     .try_collect()
//!     .await?;
//!   // After the CoW process, `scratch` and `scratch2` have diverged.
//!   assert_ne!(
//!     scratch.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!     scratch2.as_ref().as_ref_native().unwrap() as *const NativeScratch,
//!   );
//!   assert_eq!(&matches, &[("acdb", "cd")]);
//!   Ok(())
//! })}
//! # #[cfg(not(all(feature = "compiler", feature = "async")))]
//! # fn main() {}
//! ```

use crate::{
  database::Database,
  error::HyperscanRuntimeError,
  handle::Resource,
  hs,
  matchers::{
    contiguous_slice::{match_slice, Match, SliceMatcher},
    stream::{match_slice_stream, StreamMatcher},
    vectored_slice::{match_slice_vectored, VectoredMatch, VectoredMatcher},
    MatchResult,
  },
  sources::{ByteSlice, VectoredByteSlices},
  stream::LiveStream,
};
#[cfg(feature = "async")]
use crate::{
  error::ScanError,
  matchers::stream::scan::{scan_slice_stream, StreamScanMatcher},
};

#[cfg(feature = "async")]
use {
  futures_core::stream::Stream,
  tokio::{sync::mpsc, task},
};

use std::{
  mem, ops,
  ptr::{self, NonNull},
};

/// Pointer type for scratch allocations used in [`Scratch#Managing
/// Allocations`](Scratch#managing-allocations).
pub type NativeScratch = hs::hs_scratch;

/// Mutable workspace required by all search methods.
///
/// This type also serves as the most general entry point to the various
/// [synchronous](#synchronous-string-scanning) and
/// [asynchronous](#asynchronous-string-scanning) string search methods.
#[derive(Debug)]
#[repr(transparent)]
pub struct Scratch(Option<NonNull<NativeScratch>>);

unsafe impl Send for Scratch {}
unsafe impl Sync for Scratch {}

/// # Setup Methods
/// These methods create a new scratch space or initialize it against a
/// database. [`Database::allocate_scratch()`] is also provided as a convenience
/// method to combine the creation and initialization steps.
impl Scratch {
  /// Return an uninitialized scratch space without allocation.
  pub const fn blank() -> Self { Self(None) }

  /// Initialize this scratch space against the given `db`.
  ///
  /// A single scratch space can be initialized against multiple databases, but
  /// exclusive mutable access is required to perform a search, so
  /// [`Self::try_clone()`] can be used to obtain multiple copies of a
  /// multiply-initialized scratch space.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, matchers::*, state::*, sources::*};
  ///
  ///   let a_expr: Expression = "a+".parse()?;
  ///   let a_db = a_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  ///   let b_expr: Expression = "b+".parse()?;
  ///   let b_db = b_expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  ///   let mut scratch = Scratch::blank();
  ///   scratch.setup_for_db(&a_db)?;
  ///   scratch.setup_for_db(&b_db)?;
  ///
  ///   let s: ByteSlice = "ababaabb".into();
  ///
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch
  ///     .scan_sync(&a_db, s, |m| {
  ///       matches.push(unsafe { m.source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "a", "a", "aa"]);
  ///
  ///   matches.clear();
  ///   scratch
  ///     .scan_sync(&b_db, s, |m| {
  ///       matches.push(unsafe { m.source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["b", "b", "b", "bb"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn setup_for_db(&mut self, db: &Database) -> Result<(), HyperscanRuntimeError> {
    /* NB: this method always overwrites self.0, because `hs_alloc_scratch()` may
     * modify the pointer location if the scratch space needs to be resized! */
    let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
    })?;
    /* *self = unsafe { Self::from_native(scratch_ptr) }; */
    self.0 = NonNull::new(scratch_ptr);
    Ok(())
  }
}

/// # Synchronous String Scanning
/// Hyperscan's string search interface requires a C function pointer to call
/// synchronously upon each match. This guarantee of synchronous invocation
/// enables the function to mutate data under the expectation of exclusive
/// access (we formalize this guarantee as [`FnMut`]). While Rust closures
/// cannot be converted into C function pointers automatically, hyperscan also
/// passes in a `*mut c_void` context pointer to each invocation of the match
/// callback, and this can be used to hold a type-erased container for a
/// Rust-level closure.
///
/// ## Ephemeral Match Objects
/// In all of these synchronous search methods, the provided match callback `f`
/// is converted into a `dyn` reference and invoked within the C function
/// pointer provided to the hyperscan library. Match objects like [`Match`]
/// provided to the match callback are synthesized by this crate and are not
/// preserved after each invocation of `f`, so the match callback must modify
/// some external state to store match results.
impl Scratch {
  /// Synchronously scan a single contiguous string.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, matchers::*, error::*};
  ///
  ///   let a_expr: Expression = "a+".parse()?;
  ///   let b_expr: Expression = "b+".parse()?;
  ///   let flags = Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///     .with_flags([flags, flags])
  ///     .with_ids([ExprId(1), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   {
  ///     let mut f = |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     };
  ///     scratch.scan_sync(&db, "aardvark".into(), &mut f)?;
  ///     scratch.scan_sync(&db, "imbibbe".into(), &mut f)?;
  ///   }
  ///   assert_eq!(&matches, &["a", "aa", "a", "b", "b", "bb"]);
  ///
  ///   let ret = scratch.scan_sync(&db, "abwuebiaubeb".into(), |_| MatchResult::CeaseMatching);
  ///   assert!(matches![ret, Err(HyperscanRuntimeError::ScanTerminated)]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_sync<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    mut f: impl FnMut(Match<'data>) -> MatchResult,
  ) -> Result<(), HyperscanRuntimeError> {
    let mut matcher = SliceMatcher::new(data, &mut f);
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan(
        db.as_ref_native(),
        matcher.parent_slice().as_ptr(),
        matcher.parent_slice().native_len(),
        /* NB: ignoring flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice),
        mem::transmute(&mut matcher),
      )
    })
  }

  /// Synchronously scan a slice of vectored string data.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, sources::*, matchers::*};
  ///
  ///   let a_plus: Expression = "a+".parse()?;
  ///   let b_plus: Expression = "b+".parse()?;
  ///   let asdf: Expression = "asdf(.)".parse()?;
  ///   let flags = Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_plus, &b_plus, &asdf])
  ///     .with_flags([flags, flags, flags])
  ///     .with_ids([ExprId(0), ExprId(3), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::VECTORED)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let data: [ByteSlice; 4] = [
  ///     "aardvark".into(),
  ///     "imbibbe".into(),
  ///     "leas".into(),
  ///     "dfeg".into(),
  ///   ];
  ///   let mut matches: Vec<(u32, String)> = Vec::new();
  ///   scratch
  ///     .scan_sync_vectored(
  ///       &db,
  ///       data.as_ref().into(),
  ///       |VectoredMatch { id: ExpressionIndex(id), source, .. }| {
  ///         let joined = source.iter_slices()
  ///           .map(|s| unsafe { s.as_str() })
  ///           .collect::<Vec<_>>()
  ///           .concat();
  ///         matches.push((id, joined));
  ///         MatchResult::Continue
  ///     })?;
  ///   assert_eq!(matches, vec![
  ///     (0, "a".to_string()),
  ///     (0, "aa".to_string()),
  ///     (0, "a".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "bb".to_string()),
  ///     (0, "a".to_string()),
  ///     // NB: This match result crosses a slice boundary!
  ///     (2, "asdfe".to_string()),
  ///   ]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_sync_vectored<'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data, 'data>,
    mut f: impl FnMut(VectoredMatch<'data>) -> MatchResult,
  ) -> Result<(), HyperscanRuntimeError> {
    let mut matcher = VectoredMatcher::new(data, &mut f);
    let (data_pointers, lengths) = matcher.parent_slices().pointers_and_lengths();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan_vector(
        db.as_ref_native(),
        data_pointers.as_ptr(),
        lengths.as_ptr(),
        matcher.parent_slices().native_len(),
        /* NB: ignoring flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice_vectored),
        mem::transmute(&mut matcher),
      )
    })
  }

  /// Write `data` into the stream object `sink`.
  ///
  /// This method is mostly used internally; consumers of this crate will likely
  /// prefer to call
  /// [`ScratchStreamSink::scan()`](crate::stream::ScratchStreamSink::scan).
  pub fn scan_sync_stream<'data>(
    &mut self,
    live: &mut LiveStream,
    matcher: &mut StreamMatcher,
    data: ByteSlice<'data>,
  ) -> Result<(), HyperscanRuntimeError> {
    let live: &'static mut LiveStream = unsafe { mem::transmute(live) };
    let matcher: &'static mut StreamScanMatcher = unsafe { mem::transmute(matcher) };

    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_scan_stream(
        live.as_mut_native(),
        data.as_ptr(),
        data.native_len(),
        /* NB: ignore flags for now! */
        0,
        self.as_mut_native().unwrap(),
        Some(match_slice_stream),
        mem::transmute(&matcher),
      )
    })
  }

  /// Process any EOD (end-of-data) matches for the stream object `sink`.
  ///
  /// This method is mostly used internally; consumers of this crate will likely
  /// prefer to call
  /// [`ScratchStreamSink::flush_eod()`](crate::stream::ScratchStreamSink::flush_eod).
  pub fn flush_eod_sync(
    &mut self,
    live: &mut LiveStream,
    matcher: &mut StreamMatcher,
  ) -> Result<(), HyperscanRuntimeError> {
    let live: &'static mut LiveStream = unsafe { mem::transmute(live) };
    let matcher: &'static mut StreamScanMatcher = unsafe { mem::transmute(matcher) };

    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_direct_flush_stream(
        live.as_mut_native(),
        self.as_mut_native().unwrap(),
        Some(match_slice_stream),
        mem::transmute(matcher),
      )
    })
  }
}

impl Scratch {
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let msg = "aardvark";
  ///   let first_a = scratch.first_match(&db, msg.into())?.unwrap().source.as_slice();
  ///   assert_eq!(first_a, b"a");
  ///   assert_eq!(first_a.as_ptr(), msg.as_bytes().as_ptr());
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn first_match<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
  ) -> Result<Option<Match<'data>>, HyperscanRuntimeError> {
    let mut capture_text: Option<Match<'data>> = None;
    match self.scan_sync(db, data, |m| {
      debug_assert!(capture_text.is_none());
      capture_text = Some(m);
      MatchResult::CeaseMatching
    }) {
      Ok(()) => {
        assert!(capture_text.is_none());
        Ok(None)
      },
      Err(HyperscanRuntimeError::ScanTerminated) => {
        debug_assert!(capture_text.is_some());
        Ok(capture_text)
      },
      Err(e) => Err(e),
    }
  }

  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = "a+sdf".parse()?;
  ///   let db = expr.compile(Flags::default(), Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let msg = "asdf";
  ///   let m = scratch.full_match(&db, msg.into())?.unwrap().source.as_slice();
  ///   assert_eq!(m, msg.as_bytes());
  ///   assert_eq!(m.as_ptr(), msg.as_bytes().as_ptr());
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn full_match<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
  ) -> Result<Option<Match<'data>>, HyperscanRuntimeError> {
    let mut fully_matched_expr: Option<Match<'data>> = None;
    match self.scan_sync(db, data, |m| {
      debug_assert!(fully_matched_expr.is_none());
      if m.source.as_slice().len() == data.as_slice().len() {
        fully_matched_expr = Some(m);
        MatchResult::CeaseMatching
      } else {
        MatchResult::Continue
      }
    }) {
      Ok(()) => {
        assert!(fully_matched_expr.is_none());
        Ok(None)
      },
      Err(HyperscanRuntimeError::ScanTerminated) => {
        debug_assert!(fully_matched_expr.is_some());
        Ok(fully_matched_expr)
      },
      Err(e) => Err(e),
    }
  }
}

/// # Asynchronous String Scanning
/// While the synchronous search methods can be used from async or
/// multi-threaded code, a multithreaded execution environment offers particular
/// opportunities to improve search latency and/or throughput. These methods
/// are written to expose an idiomatic Rust interface for highly parallel
/// searching.
///
/// ## Minimizing Work in the Match Callback
/// Because the hyperscan match callback is always invoked synchronously, it
/// also stops the regex engine from making any further progress while it
/// executes. If the match callback does too much work before returning control
/// to the hyperscan library, this may harm search performance by thrashing the
/// processor caches or other state.`[FIXME: citation needed/benchmark this]`
///
/// ### Producer-Consumer Pattern
/// Therefore, one useful pattern is to write the match object to a queue and
/// quickly exit the match callback, then read matches from the queue in another
/// thread of control in order to decouple match processing from text searching.
/// Multi-processor systems in particular may be able to achieve higher search
/// throughput if a separate thread is used to perform further match processing
/// in parallel while a hyperscan search is executing.
///
/// **Note that the [Synchronous String Scanning
/// API](#synchronous-string-scanning) can still be used to implement
/// producer-consumer match queues!** In fact, [`Self::scan_channel()`] is
/// implemented just by writing to a queue within the match callback provided
/// to an internal [`Self::scan_sync()`] call! However, `async` streams provide
/// a natural interface to wrap the output of a queue, so the methods in this
/// section return a [`Stream`], which can be consumed or extended by external
/// code such as [`futures_util::TryStreamExt`].
///
/// ### Match Objects with Lifetimes
/// The match callbacks for these methods accept a
/// *reference* to the match object, instead of owning the match result like the
/// [`Ephemeral Match Objects`](#ephemeral-match-objects) from synchronous
/// search methods. Even though most match objects are [`Copy`] anyway, this
/// reference interface is used to clarify that the callback should only
/// determine whether to continue matching, while the underlying match object
/// will be written into the returned stream and should be retrieved from there
/// instead for further processing.
#[cfg(feature = "async")]
#[cfg_attr(docsrs, doc(cfg(feature = "async")))]
impl Scratch {
  fn into_db(db: &Database) -> usize {
    let db: *const Database = db;
    db as usize
  }

  fn from_db<'a>(db: usize) -> &'a Database { unsafe { &*(db as *const Database) } }

  fn into_scratch(scratch: &mut Scratch) -> usize {
    let scratch: *mut Scratch = scratch;
    scratch as usize
  }

  fn from_scratch<'a>(scratch: usize) -> &'a mut Scratch {
    unsafe { &mut *(scratch as *mut Scratch) }
  }

  /// Asynchronously scan a single contiguous string.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  ///   use hyperscan::{expression::*, flags::*, matchers::*, error::*};
  ///   use futures_util::TryStreamExt;
  ///
  ///   let a_expr: Expression = "a+".parse()?;
  ///   let b_expr: Expression = "b+".parse()?;
  ///   let flags = Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///     .with_flags([flags, flags])
  ///     .with_ids([ExprId(1), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let matches: Vec<&str> = scratch
  ///     .scan_channel(&db, "aardvark".into(), |_| MatchResult::Continue)
  ///     .map_ok(|Match { source, .. }| unsafe { source.as_str() })
  ///     .try_collect()
  ///     .await?;
  ///   assert_eq!(&matches, &["a", "aa", "a"]);
  ///
  ///   let matches: Vec<&str> = scratch
  ///     .scan_channel(&db, "imbibbe".into(), |_| MatchResult::Continue)
  ///     .map_ok(|Match { source, .. }| unsafe { source.as_str() })
  ///     .try_collect()
  ///     .await?;
  ///   assert_eq!(&matches, &["b", "b", "bb"]);
  ///
  ///   let ret = scratch.scan_channel(
  ///     &db,
  ///     "abwuebiaubeb".into(),
  ///     |_| MatchResult::CeaseMatching,
  ///   ).try_for_each(|_| async { Ok(()) })
  ///    .await;
  ///   assert!(matches![ret, Err(ScanError::ReturnValue(HyperscanRuntimeError::ScanTerminated))]);
  ///   Ok(())
  /// })}
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_channel<'data>(
    &mut self,
    db: &Database,
    data: ByteSlice<'data>,
    mut f: impl FnMut(&Match<'data>) -> MatchResult+Send+Sync,
  ) -> impl Stream<Item=Result<Match<'data>, ScanError>> {
    /* Convert all references into pointers cast to usize to strip lifetime
     * information so it can be moved into spawn_blocking(): */
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);
    let f: &mut (dyn FnMut(&Match<'data>) -> MatchResult+Send+Sync) = &mut f;

    /* Create a channel for both success and error results. */
    let (matches_tx, matches_rx) = mpsc::unbounded_channel();

    /* Convert parameterized lifetimes to 'static so they can be moved into
     * spawn_blocking(): */
    let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
    let f: &'static mut (dyn FnMut(&Match<'static>) -> MatchResult+Send+Sync) =
      unsafe { mem::transmute(f) };
    let matches_tx: mpsc::UnboundedSender<Result<Match<'static>, ScanError>> =
      unsafe { mem::transmute(matches_tx) };

    let matches_tx2 = matches_tx.clone();
    let scan_task = task::spawn_blocking(move || {
      /* Dereference pointer arguments. */
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);

      scratch.scan_sync(db, data, |m| {
        let result = f(&m);
        matches_tx2.send(Ok(m)).unwrap();
        result
      })
    });
    task::spawn(async move {
      match scan_task.await {
        Ok(Ok(())) => (),
        Err(e) => matches_tx.send(Err(e.into())).unwrap(),
        Ok(Err(e)) => matches_tx.send(Err(e.into())).unwrap(),
      }
    });
    async_utils::UnboundedReceiverStream(matches_rx)
  }

  /// Asynchronously scan a slice of vectored string data.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  ///   use hyperscan::{expression::*, flags::*, sources::*, matchers::*};
  ///   use futures_util::TryStreamExt;
  ///
  ///   let a_plus: Expression = "a+".parse()?;
  ///   let b_plus: Expression = "b+".parse()?;
  ///   let asdf: Expression = "asdf(.)".parse()?;
  ///   let flags = Flags::SOM_LEFTMOST;
  ///   let expr_set = ExpressionSet::from_exprs([&a_plus, &b_plus, &asdf])
  ///     .with_flags([flags, flags, flags])
  ///     .with_ids([ExprId(0), ExprId(3), ExprId(2)]);
  ///   let db = expr_set.compile(Mode::VECTORED)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let data: [ByteSlice; 4] = [
  ///     "aardvark".into(),
  ///     "imbibbe".into(),
  ///     "leas".into(),
  ///     "dfeg".into(),
  ///   ];
  ///   let matches: Vec<(u32, String)> = scratch
  ///     .scan_channel_vectored(&db, data.as_ref().into(), |_| MatchResult::Continue)
  ///     .map_ok(|VectoredMatch { id: ExpressionIndex(id), source, .. }| {
  ///       let joined = source.iter_slices()
  ///         .map(|s| unsafe { s.as_str() })
  ///         .collect::<Vec<_>>()
  ///         .concat();
  ///       (id, joined)
  ///     })
  ///     .try_collect()
  ///     .await?;
  ///   assert_eq!(matches, vec![
  ///     (0, "a".to_string()),
  ///     (0, "aa".to_string()),
  ///     (0, "a".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "b".to_string()),
  ///     (3, "bb".to_string()),
  ///     (0, "a".to_string()),
  ///     // NB: This match result crosses a slice boundary!
  ///     (2, "asdfe".to_string()),
  ///   ]);
  ///   Ok(())
  /// })}
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn scan_channel_vectored<'data>(
    &mut self,
    db: &Database,
    data: VectoredByteSlices<'data, 'data>,
    mut f: impl FnMut(&VectoredMatch<'data>) -> MatchResult+Send+Sync,
  ) -> impl Stream<Item=Result<VectoredMatch<'data>, ScanError>> {
    /* NB: while static arrays take up no extra runtime space, a ref to a
    slice
    * takes up more than pointer space! */
    static_assertions::assert_eq_size!([u8; 4], u32);
    static_assertions::assert_eq_size!(&u8, *const u8);
    static_assertions::assert_eq_size!(&[u8; 4], *const u8);
    static_assertions::const_assert!(mem::size_of::<&[u8]>() > mem::size_of::<*const u8>());
    static_assertions::assert_eq_size!(&u8, *const u8);

    /* Convert all references into pointers cast to usize to strip lifetime
     * information so it can be moved into spawn_blocking(): */
    let scratch = Self::into_scratch(self);
    let db = Self::into_db(db);
    let f: &mut (dyn FnMut(&VectoredMatch<'data>) -> MatchResult+Send+Sync) = &mut f;

    /* Create a channel for both success and error results. */
    let (matches_tx, matches_rx) = mpsc::unbounded_channel();

    /* Convert parameterized lifetimes to 'static so they can be moved into
     * spawn_blocking(): */
    let data: VectoredByteSlices<'static, 'static> = unsafe { mem::transmute(data) };
    let f: &'static mut (dyn FnMut(&VectoredMatch<'static>) -> MatchResult+Send+Sync) =
      unsafe { mem::transmute(f) };
    let matches_tx: mpsc::UnboundedSender<Result<VectoredMatch<'static>, ScanError>> =
      unsafe { mem::transmute(matches_tx) };

    let matches_tx2 = matches_tx.clone();
    let scan_task = task::spawn_blocking(move || {
      /* Dereference pointer arguments. */
      let scratch: &mut Self = Self::from_scratch(scratch);
      let db: &Database = Self::from_db(db);

      scratch.scan_sync_vectored(db, data, |m| {
        let result = f(&m);
        matches_tx2.send(Ok(m)).unwrap();
        result
      })
    });
    task::spawn(async move {
      match scan_task.await {
        Ok(Ok(())) => (),
        Err(e) => matches_tx.send(Err(e.into())).unwrap(),
        Ok(Err(e)) => matches_tx.send(Err(e.into())).unwrap(),
      }
    });
    async_utils::UnboundedReceiverStream(matches_rx)
  }

  /// Write `data` into the stream object `sink`.
  ///
  /// This method is mostly used internally; consumers of this crate will likely
  /// prefer to call
  /// [`ScratchStreamSinkChannel::scan()`](crate::stream::channel::ScratchStreamSinkChannel::scan).
  pub async fn scan_stream<'data>(
    &mut self,
    live: &mut LiveStream,
    matcher: &mut StreamScanMatcher,
    data: ByteSlice<'data>,
  ) -> Result<(), ScanError> {
    let s: &'static mut Self = unsafe { mem::transmute(self) };
    let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
    let live: &'static mut LiveStream = unsafe { mem::transmute(live) };
    let matcher: &'static mut StreamScanMatcher = unsafe { mem::transmute(matcher) };

    Ok(
      task::spawn_blocking(move || {
        HyperscanRuntimeError::from_native(unsafe {
          hs::hs_scan_stream(
            live.as_mut_native(),
            data.as_ptr(),
            data.native_len(),
            /* NB: ignore flags for now! */
            0,
            s.as_mut_native().unwrap(),
            Some(scan_slice_stream),
            mem::transmute(matcher),
          )
        })
      })
      .await??,
    )
  }

  /// Process any EOD (end-of-data) matches for the stream object `sink`.
  ///
  /// This method is mostly used internally; consumers of this crate will likely
  /// prefer to call
  /// [`ScratchStreamSinkChannel::flush_eod()`](crate::stream::channel::ScratchStreamSinkChannel::flush_eod).
  /// .
  pub async fn flush_eod(
    &mut self,
    live: &mut LiveStream,
    matcher: &mut StreamScanMatcher,
  ) -> Result<(), ScanError> {
    let s: &'static mut Self = unsafe { mem::transmute(self) };
    let live: &'static mut LiveStream = unsafe { mem::transmute(live) };
    let matcher: &'static mut StreamScanMatcher = unsafe { mem::transmute(matcher) };

    Ok(
      task::spawn_blocking(move || {
        HyperscanRuntimeError::from_native(unsafe {
          hs::hs_direct_flush_stream(
            live.as_mut_native(),
            s.as_mut_native().unwrap(),
            Some(scan_slice_stream),
            mem::transmute(matcher),
          )
        })
      })
      .await??,
    )
  }
}

/// # Managing Allocations
/// These methods provide access to the underlying memory allocation
/// containing the data for the scratch space. They can be used to
/// control the memory location used for the scratch space, or to preserve
/// scratch allocations across weird lifetime constraints.
///
/// Note that [`Self::scratch_size()`] can be used to determine the size of
/// the memory allocation pointed to by [`Self::as_ref_native()`] and
/// [`Self::as_mut_native()`].
impl Scratch {
  /* TODO: NonNull::new is not const yet! */
  /// Wrap the provided allocation `p`.
  ///
  /// # Safety
  /// The pointer `p` must be null or have been produced by
  /// [`Self::as_mut_native()`].
  ///
  /// This method also makes it especially easy to create multiple references to
  /// the same allocation, which will then cause a double free when
  /// [`Self::try_drop()`] is called more than once for the same scratch
  /// allocation. To avoid this, wrap the result in a
  /// [`ManuallyDrop`](mem::ManuallyDrop):
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, matchers::*, state::*};
  ///   use std::{mem::ManuallyDrop, ptr};
  ///
  ///   // Compile a legitimate db:
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   // Create two new references to that allocation,
  ///   // wrapped to avoid calling the drop code:
  ///   let scratch_ptr: *mut NativeScratch = scratch
  ///     .as_mut_native()
  ///     .map(|p| p as *mut NativeScratch)
  ///     .unwrap_or(ptr::null_mut());
  ///   let mut scratch_ref_1 = ManuallyDrop::new(unsafe { Scratch::from_native(scratch_ptr) });
  ///   let mut scratch_ref_2 = ManuallyDrop::new(unsafe { Scratch::from_native(scratch_ptr) });
  ///
  ///   // Both scratch references are valid and can be used for matching.
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch_ref_1
  ///     .scan_sync(&db, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   scratch_ref_2
  ///     .scan_sync(&db, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "aa", "a", "a", "aa", "a"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub unsafe fn from_native(p: *mut NativeScratch) -> Self { Self(NonNull::new(p)) }

  /// Get a read-only reference to the scratch allocation.
  ///
  /// This method is mostly used internally and converted to a nullable pointer
  /// to provide to the hyperscan native library methods.
  pub fn as_ref_native(&self) -> Option<&NativeScratch> { self.0.map(|p| unsafe { p.as_ref() }) }

  /// Get a mutable reference to the scratch allocation.
  ///
  /// The result of this method can be converted to a nullable pointer and
  /// provided to [`Self::from_native()`].
  pub fn as_mut_native(&mut self) -> Option<&mut NativeScratch> {
    self.0.map(|mut p| unsafe { p.as_mut() })
  }

  /// Return the size of the scratch allocation.
  ///
  /// Using [`Flags::UCP`](crate::flags::Flags::UCP) explodes the size of
  /// character classes, which increases the size of the scratch space:
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let ascii_db = expr.compile(Flags::default(), Mode::BLOCK)?;
  ///
  ///   let utf8_scratch = utf8_db.allocate_scratch()?;
  ///   let ascii_scratch = ascii_db.allocate_scratch()?;
  ///
  ///   // Including UTF-8 classes increases the size:
  ///   assert!(utf8_scratch.scratch_size()? > ascii_scratch.scratch_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  ///
  /// This size corresponds to the requested allocation size passed to the
  /// scratch allocator:
  ///
  ///```
  /// #[cfg(all(feature = "alloc", feature = "compiler"))]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, state::*, alloc::*};
  ///   use std::alloc::System;
  ///
  ///   // Wrap the standard Rust System allocator.
  ///   let tracker = LayoutTracker::new(System.into());
  ///   // Register it as the allocator for databases.
  ///   assert!(set_scratch_allocator(tracker)?.is_none());
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let mut utf8_scratch = utf8_db.allocate_scratch()?;
  ///
  ///   // Get the scratch allocator we just registered and view its live allocations:
  ///   let allocs = get_scratch_allocator().as_ref().unwrap().current_allocations();
  ///   // Verify that only the single known scratch was allocated:
  ///   assert_eq!(1, allocs.len());
  ///   let (p, layout) = allocs[0];
  ///   // The allocation was made 0x30 bytes to the left of the returned scratch pointer.
  ///   assert_eq!(
  ///     unsafe { p.as_ptr().add(0x30) },
  ///     utf8_scratch.as_mut_native().unwrap() as *mut NativeScratch as *mut u8,
  ///   );
  ///
  ///   // Verify that the allocation size is the same as reported:
  ///   assert_eq!(layout.size(), utf8_scratch.scratch_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(all(feature = "alloc", feature = "compiler")))]
  /// # fn main() {}
  /// ```
  pub fn scratch_size(&self) -> Result<usize, HyperscanRuntimeError> {
    match self.as_ref_native() {
      None => Ok(0),
      Some(p) => {
        let mut n: usize = 0;
        HyperscanRuntimeError::from_native(unsafe { hs::hs_scratch_size(p, &mut n) })?;
        Ok(n)
      },
    }
  }

  /// Generate a new scratch space which can be applied to the same databases as
  /// the original.
  ///
  /// This new scratch space is allocated in a new region of memory provided by
  /// the scratch allocator. This is used to implement [`Clone`].
  ///
  ///```
  /// #[cfg(all(feature = "alloc", feature = "compiler"))]
  /// fn main() -> Result<(), hyperscan::error::HyperscanError> {
  ///   use hyperscan::{expression::*, flags::*, alloc::*};
  ///   use std::alloc::System;
  ///
  ///   // Wrap the standard Rust System allocator.
  ///   let tracker = LayoutTracker::new(System.into());
  ///   // Register it as the allocator for databases.
  ///   assert!(set_scratch_allocator(tracker)?.is_none());
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let scratch1 = utf8_db.allocate_scratch()?;
  ///   let _scratch2 = scratch1.try_clone()?;
  ///
  ///   // Get the scratch allocator we just registered and view its live allocations:
  ///   let allocs = get_scratch_allocator().as_ref().unwrap().current_allocations();
  ///   // Verify that only two scratches were allocated:
  ///   assert_eq!(2, allocs.len());
  ///   let (p1, l1) = allocs[0];
  ///   let (p2, l2) = allocs[1];
  ///   assert!(p1 != p2);
  ///   assert!(l1 == l2);
  ///   Ok(())
  /// }
  /// # #[cfg(not(all(feature = "alloc", feature = "compiler")))]
  /// # fn main() {}
  /// ```
  pub fn try_clone(&self) -> Result<Self, HyperscanRuntimeError> {
    match self.as_ref_native() {
      None => Ok(Self::blank()),
      Some(p) => {
        let mut scratch_ptr = ptr::null_mut();
        HyperscanRuntimeError::from_native(unsafe { hs::hs_clone_scratch(p, &mut scratch_ptr) })?;
        Ok(Self(NonNull::new(scratch_ptr)))
      },
    }
  }

  /// Free the underlying scratch allocation.
  ///
  /// # Safety
  /// This method must be called at most once over the lifetime of each scratch
  /// allocation. It is called by default on drop, so
  /// [`ManuallyDrop`](mem::ManuallyDrop) is recommended to wrap
  /// instances that reference external data in order to avoid attempting to
  /// free the referenced data.
  ///
  /// Because the pointer returned by [`Self::as_mut_native()`] does not
  /// correspond to the entire scratch allocation, this method *must* be
  /// executed in order to avoid leaking resources associated with a scratch
  /// space. The memory *must not* be deallocated elsewhere.
  pub unsafe fn try_drop(&mut self) -> Result<(), HyperscanRuntimeError> {
    if let Some(p) = self.as_mut_native() {
      HyperscanRuntimeError::from_native(unsafe { hs::hs_free_scratch(p) })?;
    }
    Ok(())
  }
}

impl Clone for Scratch {
  fn clone(&self) -> Self { self.try_clone().unwrap() }
}

impl Resource for Scratch {
  type Error = HyperscanRuntimeError;

  unsafe fn deep_clone_into(&self, out: *mut Self) -> Result<(), Self::Error> {
    out.write(self.try_clone()?);
    Ok(())
  }

  unsafe fn sync_drop(&mut self) -> Result<(), Self::Error> { self.try_drop() }
}

impl ops::Drop for Scratch {
  fn drop(&mut self) {
    unsafe {
      self.try_drop().unwrap();
    }
  }
}

#[cfg(all(test, feature = "compiler", feature = "async"))]
mod test {
  use crate::{
    expression::Expression,
    flags::{Flags, Mode},
    matchers::MatchResult,
  };

  use futures_util::TryStreamExt;

  use std::{mem::ManuallyDrop, sync::Arc};

  #[tokio::test]
  async fn try_clone_still_valid() -> Result<(), eyre::Report> {
    let a_expr: Expression = "asdf$".parse()?;
    let db = a_expr.compile(Flags::default(), Mode::BLOCK)?;

    /* Allocate a new scratch. */
    let mut scratch = ManuallyDrop::new(db.allocate_scratch()?);
    /* Clone it. */
    let mut s2 = ManuallyDrop::new(scratch.try_clone()?);
    /* Drop the first scratch. */
    unsafe {
      scratch.try_drop()?;
    }

    /* Operate on the clone. */
    let matches: Vec<&str> = s2
      .scan_channel(&db, "asdf".into(), |_| MatchResult::Continue)
      .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
      .try_collect()
      .await?;

    assert_eq!(&matches, &["asdf"]);

    unsafe {
      s2.try_drop()?;
    }

    Ok(())
  }

  #[tokio::test]
  async fn make_mut() -> Result<(), eyre::Report> {
    let a_expr: Expression = "asdf$".parse()?;
    let db = a_expr.compile(Flags::default(), Mode::BLOCK)?;

    /* Allocate a new scratch into an Arc. */
    let scratch = Arc::new(db.allocate_scratch()?);
    /* Clone the Arc. */
    let mut s2 = Arc::clone(&scratch);

    /* Operate on the result of Arc::make_mut(). */
    let matches: Vec<&str> = Arc::make_mut(&mut s2)
      .scan_channel(&db, "asdf".into(), |_| MatchResult::Continue)
      .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
      .try_collect()
      .await?;

    assert_eq!(&matches, &["asdf"]);
    Ok(())
  }
}

/// Allocate and initialize mutable [scratch space] for the chimera library.
///
/// [scratch space]: https://intel.github.io/hyperscan/dev-reference/chimera.html#scratch-space
///
/// The chimera library also hews to the [Atypical Search
/// Interface](crate::state#atypical-search-interface) from the base
/// hyperscan library to manage mutable state (as described in [Mutable State
/// and String Searching](crate::state#mutable-state-and-string-searching)), so
/// the discussions and solutions from [Manual Cache
/// Management](crate::state#manual-cache-management) should equally apply to
/// uses of the chimera library. As with the base hyperscan library, chimera
/// provides the
/// [`ChimeraDb::allocate_scratch()`](crate::database::chimera::ChimeraDb::allocate_scratch)
/// method to encourage allocating one scratch per db, which avoids scratch
/// space contention across databases.
///
/// # Capture Groups and State Management
/// The most significant difference to note in how state is managed across these
/// libraries is a result of chimera's support for capture groups (see
/// [`crate::expression::chimera`]), which would otherwise typically require a
/// recursive search invocation to implement in the base hyperscan library. As
/// detailed in [Handling Cache Contention in
/// Rust](crate::state#handling-cache-contention-in-rust), recursive hyperscan
/// invocations require a separately allocated scratch space, so using chimera
/// for its capture group support can be one way to avoid that additional
/// mutable state, if PCRE groups are sufficiently expressive to avoid a
/// recursive search invocation.
///
/// # Copy-on-Write
/// If needed, similar [CoW approaches](crate::state#copy-on-write) as in the
/// base hyperscan library are available to chimera scratch allocations.
/// Examples are provided here using CoW techniques to perform a recursive
/// search for the sake of completeness.
///
/// ## Synchronous
/// Similarly to the [Synchronous CoW approach from
/// hyperscan](crate::state#synchronous), we can use
/// [`Rc::make_mut()`](std::rc::Rc::make_mut):
///
///```
/// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
/// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, state::chimera::*, error::chimera::*, sources::*};
/// use std::rc::Rc;
///
/// let ab_expr: ChimeraExpression = "a.*b".parse()?;
/// let ab_db = ab_expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
/// let cd_expr: ChimeraExpression = "cd".parse()?;
/// let cd_db = cd_expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
///
/// let mut scratch = ChimeraScratch::blank();
/// scratch.setup_for_db(&ab_db)?;
/// scratch.setup_for_db(&cd_db)?;
///
/// // Compose the "a.*b" and "cd" searches to form an "a(cd)b" matcher.
/// let msg = "acdb";
/// // Record the whole match and the (cd) group.
/// let mut matches: Vec<(&str, &str)> = Vec::new();
///
/// let e = |_| ChimeraMatchResult::Continue;
///
/// // Broken example to trigger ScratchInUse.
/// let s: *mut ChimeraScratch = &mut scratch;
/// // Use unsafe code to get multiple mutable references to the same allocation:
/// unsafe { &mut *s }
///   .scan_sync(&ab_db, msg.into(), |m| {
///     // Chimera was able to detect this contention!
///     // But this is described as an unreliable best-effort runtime check.
///     assert_eq!(
///       unsafe { &mut *s }.scan_sync(&cd_db, m.source, |_| ChimeraMatchResult::Continue, e),
///       Err(ChimeraRuntimeError::ScratchInUse),
///     );
///     ChimeraMatchResult::Continue
///   }, e)?;
///
/// // Try again using Rc::make_mut() to avoid contention:
/// let mut scratch = Rc::new(scratch);
/// // This is a shallow copy pointing to the same memory:
/// let mut scratch2 = scratch.clone();
/// // Currently, these point to the same allocation:
/// assert_eq!(
///   scratch.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
///   scratch2.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
/// );
/// // When Rc::make_mut() is first called within the match callback,
/// // `scratch2` will call ChimeraScratch::try_clone() to generate
/// // a new heap allocation, which `scratch2` then becomes the exclusive owner of.
///
/// Rc::make_mut(&mut scratch)
///   // First search for "a.*b":
///   .scan_sync(&ab_db, msg.into(), |outer_match| {
///     // Strip the "^a" and "b$" in order to perform a search of the ".*":
///     let inner_group: ByteSlice = unsafe { outer_match.source.as_str() }
///       .strip_prefix('a').unwrap()
///       .strip_suffix('b').unwrap()
///       .into();
///     // Perform the inner search, cloning the scratch space upon first use:
///     if let Some(m) = Rc::make_mut(&mut scratch2)
///       // Now search for "cd" within the text matching ".*" from the original pattern:
///       .full_match(&cd_db, inner_group).unwrap() {
///       matches.push(unsafe { (outer_match.source.as_str(), m.source.as_str()) });
///     }
///     ChimeraMatchResult::Continue
///   }, e)?;
///
/// // At least one match was found, so we know the inner matcher was invoked,
/// // and that the lazy clone has occurred.
/// assert!(!matches.is_empty());
/// // After the CoW process, `scratch` and `scratch2` have diverged.
/// assert_ne!(
///   scratch.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
///   scratch2.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
/// );
/// assert_eq!(&matches, &[("acdb", "cd")]);
/// # Ok(())
/// # }
/// # #[cfg(not(feature = "compiler"))]
/// # fn main() {}
/// ```
///
/// ## Asynchronous
/// For asynchronous or multi-threaded use cases, we can adopt the [Asynchronous
/// CoW approach from hyperscan](crate::state#asynchronous) and use
/// [`Arc::make_mut()`](std::sync::Arc::make_mut):
///
///```
/// #[cfg(feature = "async")]
/// fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> { tokio_test::block_on(async {
///   use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, state::chimera::*, sources::*};
///   use futures_util::TryStreamExt;
///   use std::sync::Arc;
///
///   let ab_expr: ChimeraExpression = "a.*b".parse()?;
///   let ab_db = ab_expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
///   let cd_expr: ChimeraExpression = "cd".parse()?;
///   let cd_db = cd_expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
///
///   let mut scratch = ChimeraScratch::blank();
///   scratch.setup_for_db(&ab_db)?;
///   scratch.setup_for_db(&cd_db)?;
///
///   let msg = "acdb";
///   let e = |_: &_| ChimeraMatchResult::Continue;
///
///   // Use Arc::make_mut() to lazily clone.
///   let mut scratch = Arc::new(scratch);
///   // This will only call the underlying ChimeraScratch::try_clone()
///   // if the outer scan matches and Arc::make_mut() is called:
///   let mut scratch2 = scratch.clone();
///   // Currently, these point to the same allocation:
///   assert_eq!(
///     scratch.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
///     scratch2.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
///   );
///
///   let matches: Vec<(&str, &str)> = Arc::make_mut(&mut scratch)
///     // Match "a.*b":
///     .scan_channel(&ab_db, msg.into(), |_| ChimeraMatchResult::Continue, e)
///     .map_ok(|outer_match| {
///       // Strip the "^a" and "b$" in order to perform a search of the ".*":
///       let inner_group: ByteSlice = unsafe { outer_match.source.as_str() }
///         .strip_prefix('a').unwrap()
///         .strip_suffix('b').unwrap()
///         .into();
///       // This callback runs in parallel with the .scan_channel() task,
///       // so it needs its own exclusive mutable access:
///       Arc::make_mut(&mut scratch2)
///         // Perform another scan on the contents of the match:
///         .scan_channel(&cd_db, inner_group, |_| ChimeraMatchResult::Continue, e)
///         // Return both inner and outer match objects:
///         .map_ok(move |captured_match| (outer_match.clone(), captured_match))
///     })
///     // Our .map_ok() method itself returns a stream, so flatten them out:
///     .try_flatten()
///     // Extract match text from match objects:
///     .map_ok(|(outer_match, captured_match)| unsafe { (
///       outer_match.source.as_str(),
///       captured_match.source.as_str(),
///      ) })
///     .try_collect()
///     .await?;
///   // After the CoW process, `scratch` and `scratch2` have diverged.
///   assert_ne!(
///     scratch.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
///     scratch2.as_ref().as_ref_native().unwrap() as *const NativeChimeraScratch,
///   );
///   assert_eq!(&matches, &[("acdb", "cd")]);
///   Ok(())
/// })}
/// # #[cfg(not(feature = "async"))]
/// # fn main() {}
/// ```
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;
  use crate::{database::chimera::ChimeraDb, error::chimera::*, matchers::chimera::*};

  /// Pointer type for scratch allocations used in [`ChimeraScratch#Managing
  /// Allocations`](ChimeraScratch#managing-allocations).
  pub type NativeChimeraScratch = hs::ch_scratch;

  /// Mutable workspace required by all search methods.
  ///
  /// This type also serves as the most general entry point to the various
  /// [synchronous](#synchronous-string-scanning) and
  /// [asynchronous](#asynchronous-string-scanning) string search methods.
  #[derive(Debug)]
  #[repr(transparent)]
  pub struct ChimeraScratch(Option<NonNull<NativeChimeraScratch>>);

  unsafe impl Send for ChimeraScratch {}
  unsafe impl Sync for ChimeraScratch {}

  /// # Setup Methods
  /// These methods create a new scratch space or initialize it against a
  /// database. [`ChimeraDb::allocate_scratch()`] is also provided as a
  /// convenience method to combine the creation and initialization steps.
  impl ChimeraScratch {
    /// Return an uninitialized scratch space without allocation.
    pub const fn blank() -> Self { Self(None) }

    /// Initialize this scratch space against the given `db`.
    ///
    /// A single scratch space can be initialized against multiple databases,
    /// but exclusive mutable access is required to perform a search, so
    /// [`Self::try_clone()`] can be used to obtain multiple copies of a
    /// multiply-initialized scratch space.
    ///
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, state::chimera::*, sources::*};
    ///
    /// let a_expr: ChimeraExpression = "a+".parse()?;
    /// let a_db = a_expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    ///
    /// let b_expr: ChimeraExpression = "b+".parse()?;
    /// let b_db = b_expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    ///
    /// let mut scratch = ChimeraScratch::blank();
    /// scratch.setup_for_db(&a_db)?;
    /// scratch.setup_for_db(&b_db)?;
    ///
    /// let s: ByteSlice = "ababaabb".into();
    ///
    /// let mut matches: Vec<&str> = Vec::new();
    /// let e = |_| ChimeraMatchResult::Continue;
    /// scratch
    ///   .scan_sync(&a_db, s, |m| {
    ///     matches.push(unsafe { m.source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// assert_eq!(&matches, &["a", "a", "aa"]);
    ///
    /// matches.clear();
    /// scratch
    ///   .scan_sync(&b_db, s, |m| {
    ///     matches.push(unsafe { m.source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// assert_eq!(&matches, &["b", "b", "bb"]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn setup_for_db(&mut self, db: &ChimeraDb) -> Result<(), ChimeraRuntimeError> {
      let mut scratch_ptr = self.0.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_alloc_scratch(db.as_ref_native(), &mut scratch_ptr)
      })?;
      self.0 = NonNull::new(scratch_ptr);
      Ok(())
    }
  }

  /// # Synchronous String Scanning
  /// The chimera string search interface is very similar to the [Synchronous
  /// String Scanning](super::Scratch#synchronous-string-scanning) API
  /// provided by the base hyperscan library. The biggest difference is that
  /// chimera requires two separate callbacks, one for match objects and one
  /// for PCRE match errors (which can often simply be ignored). Chimera also
  /// does not support vectored or stream searches.
  impl ChimeraScratch {
    /// Synchronously scan a single contiguous string.
    ///
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*};
    ///
    /// let expr: ChimeraExpression = "a+(.)".parse()?;
    /// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::GROUPS)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let mut matches: Vec<(&str, &str)> = Vec::new();
    /// scratch.scan_sync(
    ///   &db,
    ///   "aardvark".into(),
    ///   |ChimeraMatch { source, captures, .. }| {
    ///     matches.push(unsafe { (source.as_str(), captures.unwrap()[1].unwrap().as_str()) });
    ///     ChimeraMatchResult::Continue
    ///   },
    ///   |_| ChimeraMatchResult::Continue,
    ///  )?;
    /// assert_eq!(&matches, &[("aar", "r"), ("ar", "r")]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn scan_sync<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
      mut m: impl FnMut(ChimeraMatch<'data>) -> ChimeraMatchResult,
      mut e: impl FnMut(ChimeraMatchError) -> ChimeraMatchResult,
    ) -> Result<(), ChimeraRuntimeError> {
      let mut matcher = ChimeraSyncSliceMatcher::new(data, &mut m, &mut e);
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_scan(
          db.as_ref_native(),
          matcher.parent_slice().as_ptr(),
          matcher.parent_slice().native_len(),
          /* NB: ignoring flags for now! */
          0,
          self.as_mut_native().unwrap(),
          Some(match_chimera_slice),
          Some(error_callback_chimera),
          mem::transmute(&mut matcher),
        )
      })
    }
  }

  impl ChimeraScratch {
    pub fn first_match<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
    ) -> Result<Option<ChimeraMatch<'data>>, ChimeraRuntimeError> {
      let mut capture: Option<ChimeraMatch<'data>> = None;
      match self.scan_sync(
        db,
        data,
        |m| {
          debug_assert!(capture.is_none());
          capture = Some(m);
          ChimeraMatchResult::Terminate
        },
        |_| ChimeraMatchResult::Continue,
      ) {
        Ok(()) => {
          assert!(capture.is_none());
          Ok(None)
        },
        Err(ChimeraRuntimeError::ScanTerminated) => {
          debug_assert!(capture.is_some());
          Ok(capture)
        },
        Err(e) => Err(e),
      }
    }

    pub fn full_match<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
    ) -> Result<Option<ChimeraMatch<'data>>, ChimeraRuntimeError> {
      let mut fully_matched_expr: Option<ChimeraMatch<'data>> = None;
      match self.scan_sync(
        db,
        data,
        |m| {
          debug_assert!(fully_matched_expr.is_none());
          if m.source.as_slice().len() == data.as_slice().len() {
            fully_matched_expr = Some(m);
            ChimeraMatchResult::Terminate
          } else {
            ChimeraMatchResult::Continue
          }
        },
        |_| ChimeraMatchResult::Continue,
      ) {
        Ok(()) => {
          assert!(fully_matched_expr.is_none());
          Ok(None)
        },
        Err(ChimeraRuntimeError::ScanTerminated) => {
          debug_assert!(fully_matched_expr.is_some());
          Ok(fully_matched_expr)
        },
        Err(e) => Err(e),
      }
    }
  }

  /// # Asynchronous String Scanning
  /// The chimera `async` string search interface is very similar to the
  /// [Asynchronous String
  /// Scanning](super::Scratch#asynchronous-string-scanning) API provided by the
  /// base hyperscan library, and the async match callbacks also take
  /// references before writing match objects to the returned stream. The
  /// biggest difference is that vectored and stream searching are not
  /// supported.
  impl ChimeraScratch {
    fn into_db(db: &ChimeraDb) -> usize {
      let db: *const ChimeraDb = db;
      db as usize
    }

    fn from_db<'a>(db: usize) -> &'a ChimeraDb { unsafe { &*(db as *const ChimeraDb) } }

    fn into_scratch(scratch: &mut ChimeraScratch) -> usize {
      let scratch: *mut ChimeraScratch = scratch;
      scratch as usize
    }

    fn from_scratch<'a>(scratch: usize) -> &'a mut ChimeraScratch {
      unsafe { &mut *(scratch as *mut ChimeraScratch) }
    }

    /// Asynchronously scan a single contiguous string.
    ///
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// # tokio_test::block_on(async {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, error::chimera::*};
    /// use futures_util::TryStreamExt;
    ///
    /// let expr: ChimeraExpression = "a+(.)".parse()?;
    /// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::GROUPS)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let m = |_: &ChimeraMatch| ChimeraMatchResult::Continue;
    /// let e = |_: &ChimeraMatchError| ChimeraMatchResult::Continue;
    /// let matches: Vec<(&str, &str)> = scratch.scan_channel(&db, "aardvark".into(), m, e)
    ///  .map_ok(|ChimeraMatch { source, captures, .. }| {
    ///    unsafe { (source.as_str(), captures.unwrap()[1].unwrap().as_str()) }
    ///  })
    ///  .try_collect()
    ///  .await?;
    /// assert_eq!(&matches, &[("aar", "r"), ("ar", "r")]);
    /// # Ok(())
    /// # })}
    /// ```
    #[cfg(feature = "async")]
    #[cfg_attr(docsrs, doc(cfg(feature = "async")))]
    pub fn scan_channel<'data>(
      &mut self,
      db: &ChimeraDb,
      data: ByteSlice<'data>,
      mut m: impl FnMut(&ChimeraMatch<'data>) -> ChimeraMatchResult+Send+Sync,
      mut e: impl FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync,
    ) -> impl Stream<Item=Result<ChimeraMatch<'data>, ChimeraScanError>> {
      /* Convert all references into pointers cast to usize to strip lifetime
       * information so it can be moved into spawn_blocking(): */
      let scratch = Self::into_scratch(self);
      let db = Self::into_db(db);
      let m: &mut (dyn FnMut(&ChimeraMatch<'data>) -> ChimeraMatchResult+Send+Sync) = &mut m;
      let e: &mut (dyn FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync) = &mut e;

      /* Create a channel for all success and error results. */
      let (matches_tx, matches_rx) = mpsc::unbounded_channel();

      /* Convert parameterized lifetimes to 'static so they can be moved into
       * spawn_blocking(): */
      let data: ByteSlice<'static> = unsafe { mem::transmute(data) };
      let m: &'static mut (dyn FnMut(&ChimeraMatch<'static>) -> ChimeraMatchResult+Send+Sync) =
        unsafe { mem::transmute(m) };
      let e: &'static mut (dyn FnMut(&ChimeraMatchError) -> ChimeraMatchResult+Send+Sync) =
        unsafe { mem::transmute(e) };
      let matches_tx: mpsc::UnboundedSender<Result<ChimeraMatch<'static>, ChimeraScanError>> =
        unsafe { mem::transmute(matches_tx) };

      let matches_tx2 = matches_tx.clone();
      let scan_task = task::spawn_blocking(move || {
        /* Dereference pointer arguments. */
        let scratch: &mut Self = Self::from_scratch(scratch);
        let db: &ChimeraDb = Self::from_db(db);

        scratch.scan_sync(
          db,
          data,
          |cm| {
            let result = m(&cm);
            matches_tx2.send(Ok(cm)).unwrap();
            result
          },
          |ce| {
            let result = e(&ce);
            matches_tx2.send(Err(ce.into())).unwrap();
            result
          },
        )
      });
      task::spawn(async move {
        match scan_task.await {
          Ok(Ok(())) => (),
          Err(e) => matches_tx.send(Err(e.into())).unwrap(),
          Ok(Err(e)) => matches_tx.send(Err(e.into())).unwrap(),
        }
      });
      async_utils::UnboundedReceiverStream(matches_rx)
    }
  }

  /// # Managing Allocations
  /// These methods provide access to the underlying memory allocation
  /// containing the data for the scratch space. They can be used to
  /// control the memory location used for the scratch space, or to preserve
  /// scratch allocations across weird lifetime constraints.
  ///
  /// Note that [`Self::scratch_size()`] can be used to determine the size of
  /// the memory allocation pointed to by [`Self::as_ref_native()`] and
  /// [`Self::as_mut_native()`].
  impl ChimeraScratch {
    /* TODO: NonNull::new is not const yet! */
    /// Wrap the provided allocation `p`.
    ///
    /// # Safety
    /// The pointer `p` must be null or have been produced by
    /// [`Self::as_mut_native()`].
    ///
    /// This method also makes it especially easy to create multiple references
    /// to the same allocation, which will then cause a double free when
    /// [`Self::try_drop()`] is called more than once for the same scratch
    /// allocation. To avoid this, wrap the result in a
    /// [`ManuallyDrop`](mem::ManuallyDrop):
    ///
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, state::chimera::*};
    /// use std::{mem::ManuallyDrop, ptr};
    ///
    /// // Compile a legitimate db:
    /// let expr: ChimeraExpression = "a+".parse()?;
    /// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// // Create two new references to that allocation,
    /// // wrapped to avoid calling the drop code:
    /// let scratch_ptr: *mut NativeChimeraScratch = scratch
    ///   .as_mut_native()
    ///   .map(|p| p as *mut NativeChimeraScratch)
    ///   .unwrap_or(ptr::null_mut());
    /// let mut scratch_ref_1 = ManuallyDrop::new(unsafe {
    ///   ChimeraScratch::from_native(scratch_ptr)
    /// });
    /// let mut scratch_ref_2 = ManuallyDrop::new(unsafe {
    ///   ChimeraScratch::from_native(scratch_ptr)
    /// });
    ///
    /// // Both scratch references are valid and can be used for matching.
    /// let mut matches: Vec<&str> = Vec::new();
    /// let e = |_| ChimeraMatchResult::Continue;
    /// scratch_ref_1
    ///   .scan_sync(&db, "aardvark".into(), |ChimeraMatch { source, .. }| {
    ///     matches.push(unsafe { source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// scratch_ref_2
    ///   .scan_sync(&db, "aardvark".into(), |ChimeraMatch { source, .. }| {
    ///     matches.push(unsafe { source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// assert_eq!(&matches, &["aa", "a", "aa", "a"]);
    /// # Ok(())
    /// # }
    /// ```
    pub unsafe fn from_native(p: *mut NativeChimeraScratch) -> Self { Self(NonNull::new(p)) }

    /// Get a read-only reference to the scratch allocation.
    ///
    /// This method is mostly used internally and converted to a nullable
    /// pointer to provide to the chimera native library methods.
    pub fn as_ref_native(&self) -> Option<&NativeChimeraScratch> {
      self.0.map(|p| unsafe { p.as_ref() })
    }

    /// Get a mutable reference to the scratch allocation.
    ///
    /// The result of this method can be converted to a nullable pointer and
    /// provided to [`Self::from_native()`].
    pub fn as_mut_native(&mut self) -> Option<&mut NativeChimeraScratch> {
      self.0.map(|mut p| unsafe { p.as_mut() })
    }

    /// Return the size of the scratch allocation.
    ///
    /// Using [`Flags::UCP`](crate::flags::Flags::UCP) explodes the size of
    /// character classes, which increases the size of the scratch space:
    ///
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*};
    ///
    /// let expr: ChimeraExpression = r"\w".parse()?;
    /// let utf8_db = expr.compile(
    ///   ChimeraFlags::UTF8 | ChimeraFlags::UCP,
    ///   ChimeraMode::NOGROUPS,
    /// )?;
    /// let ascii_db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    ///
    /// let utf8_scratch = utf8_db.allocate_scratch()?;
    /// let ascii_scratch = ascii_db.allocate_scratch()?;
    ///
    /// // Including UTF-8 classes increases the size:
    /// assert!(utf8_scratch.scratch_size()? > ascii_scratch.scratch_size()?);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// This size corresponds to the requested allocation sizes passed to the
    /// scratch allocator:
    ///
    ///```
    /// #[cfg(feature = "alloc")]
    /// fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    ///   use hyperscan::{expression::chimera::*, flags::chimera::*, alloc::{*, chimera::*}};
    ///   use std::alloc::System;
    ///
    ///   // Wrap the standard Rust System allocator.
    ///   let tracker = LayoutTracker::new(System.into());
    ///   // Register it as the allocator for databases.
    ///   assert!(set_chimera_scratch_allocator(tracker)?.is_none());
    ///
    ///   let expr: ChimeraExpression = r"\w".parse()?;
    ///   let utf8_db = expr.compile(
    ///     ChimeraFlags::UTF8 | ChimeraFlags::UCP,
    ///     ChimeraMode::NOGROUPS,
    ///   )?;
    ///   let utf8_scratch = utf8_db.allocate_scratch()?;
    ///
    ///   // Get the scratch allocator we just registered and view its live allocations:
    ///   let allocs = get_chimera_scratch_allocator().as_ref().unwrap().current_allocations();
    ///   // Verify that only the single known scratch was allocated:
    ///   assert_eq!(2, allocs.len());
    ///   let (_p1, l1) = allocs[0];
    ///   let (_p2, l2) = allocs[1];
    ///
    ///   // Verify that the sum of allocation sizes is the same as reported:
    ///   assert_eq!(l1.size() + l2.size(), utf8_scratch.scratch_size()?);
    ///   Ok(())
    /// }
    /// # #[cfg(not(feature = "alloc"))]
    /// # fn main() {}
    /// ```
    pub fn scratch_size(&self) -> Result<usize, ChimeraRuntimeError> {
      match self.as_ref_native() {
        None => Ok(0),
        Some(p) => {
          let mut n: usize = 0;
          ChimeraRuntimeError::from_native(unsafe { hs::ch_scratch_size(p, &mut n) })?;
          Ok(n)
        },
      }
    }

    /// Generate a new scratch space which can be applied to the same databases
    /// as the original.
    ///
    /// This new scratch space is allocated in a new region of memory provided
    /// by the scratch allocator. This is used to implement [`Clone`].
    ///
    ///```
    /// #[cfg(feature = "alloc")]
    /// fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    ///   use hyperscan::{expression::chimera::*, flags::chimera::*, alloc::{*, chimera::*}};
    ///   use std::alloc::System;
    ///
    ///   // Wrap the standard Rust System allocator.
    ///   let tracker = LayoutTracker::new(System.into());
    ///   // Register it as the allocator for databases.
    ///   assert!(set_chimera_scratch_allocator(tracker)?.is_none());
    ///
    ///   let expr: ChimeraExpression = r"\w".parse()?;
    ///   let utf8_db = expr.compile(
    ///     ChimeraFlags::UTF8 | ChimeraFlags::UCP,
    ///     ChimeraMode::NOGROUPS,
    ///   )?;
    ///   let scratch1 = utf8_db.allocate_scratch()?;
    ///   let _scratch2 = scratch1.try_clone()?;
    ///
    ///   // Get the scratch allocator we just registered and view its live allocations:
    ///   let allocs = get_chimera_scratch_allocator().as_ref().unwrap().current_allocations();
    ///   // Verify that only two scratches were allocated:
    ///   assert_eq!(4, allocs.len());
    ///   let (p1, l1) = allocs[0];
    ///   let (p2, l2) = allocs[1];
    ///   let (p3, l3) = allocs[2];
    ///   let (p4, l4) = allocs[3];
    ///   assert!(p1 != p3);
    ///   assert!(p2 != p4);
    ///   assert!(l1 == l3);
    ///   assert!(l2 == l4);
    ///   Ok(())
    /// }
    /// # #[cfg(not(feature = "alloc"))]
    /// # fn main() {}
    /// ```
    pub fn try_clone(&self) -> Result<Self, ChimeraRuntimeError> {
      match self.as_ref_native() {
        None => Ok(Self::blank()),
        Some(p) => {
          let mut scratch_ptr = ptr::null_mut();
          ChimeraRuntimeError::from_native(unsafe { hs::ch_clone_scratch(p, &mut scratch_ptr) })?;
          Ok(Self(NonNull::new(scratch_ptr)))
        },
      }
    }

    /// Free the underlying scratch allocation.
    ///
    /// # Safety
    /// This method must be called at most once over the lifetime of each
    /// scratch allocation. It is called by default on drop, so
    /// [`ManuallyDrop`](mem::ManuallyDrop) is recommended to wrap
    /// instances that reference external data in order to avoid attempting to
    /// free the referenced data.
    ///
    /// Because the pointer returned by [`Self::as_mut_native()`] does not
    /// correspond to the entire scratch allocation, this method *must* be
    /// executed in order to avoid leaking resources associated with a scratch
    /// space. The memory *must not* be deallocated elsewhere.
    pub unsafe fn try_drop(&mut self) -> Result<(), ChimeraRuntimeError> {
      if let Some(p) = self.as_mut_native() {
        ChimeraRuntimeError::from_native(unsafe { hs::ch_free_scratch(p) })?;
      }
      Ok(())
    }
  }

  impl Clone for ChimeraScratch {
    fn clone(&self) -> Self { self.try_clone().unwrap() }
  }

  impl Resource for ChimeraScratch {
    type Error = ChimeraRuntimeError;

    unsafe fn deep_clone_into(&self, out: *mut Self) -> Result<(), Self::Error> {
      out.write(self.try_clone()?);
      Ok(())
    }

    unsafe fn sync_drop(&mut self) -> Result<(), Self::Error> { self.try_drop() }
  }

  impl ops::Drop for ChimeraScratch {
    fn drop(&mut self) {
      unsafe {
        self.try_drop().unwrap();
      }
    }
  }
}

#[cfg(feature = "async")]
mod async_utils {
  use futures_core::stream::Stream;
  use tokio::sync::mpsc;

  use std::{
    pin::Pin,
    task::{Context, Poll},
  };

  /* Reimplementation of tokio_stream::wrappers::UnboundedReceiverStream. */
  #[derive(Debug)]
  #[repr(transparent)]
  pub struct UnboundedReceiverStream<T>(pub mpsc::UnboundedReceiver<T>);

  impl<T> Stream for UnboundedReceiverStream<T> {
    type Item = T;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
      self.0.poll_recv(cx)
    }
  }
}

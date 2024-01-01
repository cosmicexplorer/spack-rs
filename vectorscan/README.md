vectorscan
==========

A Rust wrapper for the [vectorscan](https://www.vectorcamp.gr/vectorscan/) C++ regex library.

# Quirks
The vectorscan[^vectorscan] library (originally hyperscan[^hyperscan], from Intel) supports
high-performance pattern matching using a subset of PCRE syntax. It was
originally written for extremely low-latency network traffic monitoring, so
it has some interface quirks that may be unfamiliar:
- **Vectorscan Callback API:** Matches are "returned" to the user when
  vectorscan executes a user-provided C ABI method call, so overlapping
  matches and other interactive feedback with the matching engine are much
  easier to support compared to a synchronous method call.
- **Highly Expressive Pattern Set Matching:** [`expression::ExpressionSet`]
  supports the full range of searching and matching operations available to
  individual [`expression::Expression`] instances. This is rare: most other
  regex engines e.g. do not support finding match offsets, but instead only
  which expressions in a set matched.
- **Mutable State and String Searching:** Vectorscan requires the user to
  explicitly provide a "scratch" space with [`state::Scratch`] to each
  search method. This state is not very large, but most other regex engines
  attempt to present an interface without any mutable state, even if
  internally they use constructions like lazy DFAs.

[^vectorscan]: https://github.com/VectorCamp/vectorscan
[^hyperscan]: https://github.com/intel/hyperscan

# Feature Flags
This library uses [`spack-rs`](https://docs.rs/spack-rs) to configure the build of the
vectorscan codebase using [`spack`](https://spack.io), so it can be precise about which native
dependencies it brings in:
- **`"static"` (default):** link against vectorscan statically. Conflicts
  with `"dynamic"`.
- **`"dynamic"`:** link against vectorscan dynamically. Conflicts with
  `"static"`, `"chimera"`, and `"alloc"`. Because of `spack`'s caching and
  RPATH rewriting, the same dynamic library can be shared by every
  dependency of this crate.
- **`"compiler"` (default):** whether to bring in the entire `libhs`
  library, or just `libhs_runtime`, which is unable to compile patterns
  but can deserialize them. This significantly reduces the size of the
  code added to the binary.
- **`"chimera"`:** whether to link against PCRE and add in extra vectorscan
  code to provide the chimera PCRE compatible search library. Conflicts with
  `"dynamic"` and requires `"compiler"`.

Feature flags are also used to gate certain functionality to minimize
external dependencies when not in use:
- **`"alloc"`:** hook into vectorscan's dynamic memory allocation with
  [`crate::alloc`]. Requires `"static"` due to modifying process-global
  hooks.
- **`"stream"` (default):** supports stream parsing with [`crate::stream`].
- **`"vectored"` (default):** supports vectored mode parsing with
  [`Mode::VECTORED`].
- **`"catch-unwind"` (default):** catches Rust panics in the match callback
  before they bubble back up to vectorscan to produce undefined behavior.
- **`"async"`:** provides an `async` interface over vectorscan's quirky
  callback API using [`tokio`].
- **`"tokio-impls"`:** implements [`tokio::io::AsyncWrite`] for stream
  parsers in [`crate::stream::channel::AsyncStreamWriter`].

# License
[BSD-3-Clause](./LICENSE), to match the upstream vectorscan project.

/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
#![feature(const_nonnull_new)]
#![feature(const_mut_refs)]
#![feature(const_pin)]
#![feature(trait_alias)]
#![feature(const_maybe_uninit_zeroed)]

#[allow(unused, non_camel_case_types)]
mod bindings;

pub mod error;

pub mod flags;

pub mod state;

pub mod expression;

pub mod database;

pub mod matchers;

pub(crate) use bindings as hs;

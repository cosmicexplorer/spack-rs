/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

/// This module stubs out the values from the native bindings that are exposed
/// to the `hyperscan-async` crate's public API (which are needed to generate
/// docs). They are never used at runtime.
#[allow(warnings)]
pub mod root {
  pub const HS_MAJOR: u8 = 5;
  pub const HS_MINOR: u8 = 4;
  pub const HS_PATCH: u8 = 2;
  pub const HS_SUCCESS: u8 = 0;
  pub const HS_INVALID: i8 = -1;
  pub const HS_NOMEM: i8 = -2;
  pub const HS_SCAN_TERMINATED: i8 = -3;
  pub const HS_COMPILER_ERROR: i8 = -4;
  pub const HS_DB_VERSION_ERROR: i8 = -5;
  pub const HS_DB_PLATFORM_ERROR: i8 = -6;
  pub const HS_DB_MODE_ERROR: i8 = -7;
  pub const HS_BAD_ALIGN: i8 = -8;
  pub const HS_BAD_ALLOC: i8 = -9;
  pub const HS_SCRATCH_IN_USE: i8 = -10;
  pub const HS_ARCH_ERROR: i8 = -11;
  pub const HS_INSUFFICIENT_SPACE: i8 = -12;
  pub const HS_UNKNOWN_ERROR: i8 = -13;
  pub const HS_EXT_FLAG_MIN_OFFSET: u8 = 1;
  pub const HS_EXT_FLAG_MAX_OFFSET: u8 = 2;
  pub const HS_EXT_FLAG_MIN_LENGTH: u8 = 4;
  pub const HS_EXT_FLAG_EDIT_DISTANCE: u8 = 8;
  pub const HS_EXT_FLAG_HAMMING_DISTANCE: u8 = 16;
  pub const HS_FLAG_CASELESS: u8 = 1;
  pub const HS_FLAG_DOTALL: u8 = 2;
  pub const HS_FLAG_MULTILINE: u8 = 4;
  pub const HS_FLAG_SINGLEMATCH: u8 = 8;
  pub const HS_FLAG_ALLOWEMPTY: u8 = 16;
  pub const HS_FLAG_UTF8: u8 = 32;
  pub const HS_FLAG_UCP: u8 = 64;
  pub const HS_FLAG_PREFILTER: u8 = 128;
  pub const HS_FLAG_SOM_LEFTMOST: u16 = 256;
  pub const HS_FLAG_COMBINATION: u16 = 512;
  pub const HS_FLAG_QUIET: u16 = 1024;
  pub const HS_CPU_FEATURES_AVX2: u8 = 4;
  pub const HS_CPU_FEATURES_AVX512: u8 = 8;
  pub const HS_CPU_FEATURES_AVX512VBMI: u8 = 16;
  pub const HS_TUNE_FAMILY_GENERIC: u8 = 0;
  pub const HS_TUNE_FAMILY_SNB: u8 = 1;
  pub const HS_TUNE_FAMILY_IVB: u8 = 2;
  pub const HS_TUNE_FAMILY_HSW: u8 = 3;
  pub const HS_TUNE_FAMILY_SLM: u8 = 4;
  pub const HS_TUNE_FAMILY_BDW: u8 = 5;
  pub const HS_TUNE_FAMILY_SKL: u8 = 6;
  pub const HS_TUNE_FAMILY_SKX: u8 = 7;
  pub const HS_TUNE_FAMILY_GLM: u8 = 8;
  pub const HS_TUNE_FAMILY_ICL: u8 = 9;
  pub const HS_TUNE_FAMILY_ICX: u8 = 10;
  pub const HS_MODE_BLOCK: u8 = 1;
  pub const HS_MODE_NOSTREAM: u8 = 1;
  pub const HS_MODE_STREAM: u8 = 2;
  pub const HS_MODE_VECTORED: u8 = 4;
  pub const HS_MODE_SOM_HORIZON_LARGE: u32 = 16777216;
  pub const HS_MODE_SOM_HORIZON_MEDIUM: u32 = 33554432;
  pub const HS_MODE_SOM_HORIZON_SMALL: u32 = 67108864;
  pub const HS_OFFSET_PAST_HORIZON: i8 = -1;
  pub struct hs_database;
  pub struct hs_error_t;
  pub struct hs_platform_info;
  pub struct hs_compile_error;
  pub struct hs_expr_ext;
  pub struct hs_expr_info;
  pub struct hs_scratch;
  pub struct hs_stream;
}

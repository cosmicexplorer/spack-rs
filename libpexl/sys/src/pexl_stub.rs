/* Copyright 2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#![allow(warnings)]

/// This module stubs out the values from the native bindings that are exposed
/// to the `libpexl` crate's public API (which are needed to generate
/// docs). They are never used at runtime.

pub const pexl_Index_MAX: u32 = 2147483647;
pub const pexl_Index_MIN: i32 = -2147483648;
pub const pexl_Index_FMT: &[u8; 2] = b"d\0";
pub const pexl_Index_UNDEF: i8 = -1;
pub const pexl_Position_FMT: &[u8; 3] = b"ld\0";
pub const pexl_Number_FMT: &[u8; 3] = b"ld\0";
pub type pexl_Byte = ::std::os::raw::c_uchar;
pub type pexl_Codepoint = u32;
pub type pexl_Index = i32;
pub type pexl_Position = i64;
pub type pexl_Number = i64;
pub const pexlEncoderID_PEXL_NO_ENCODER: pexlEncoderID = 0;
pub const pexlEncoderID_PEXL_DEBUG_ENCODER: pexlEncoderID = 1;
pub const pexlEncoderID_PEXL_TREE_ENCODER: pexlEncoderID = 2;
pub type pexlEncoderID = ::std::os::raw::c_uint;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_Match {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_MatchNode {
  _unused: [u8; 0],
}
extern "C" {
  pub fn pexl_new_Match(e: pexlEncoderID) -> *mut pexl_Match;
}
extern "C" {
  pub fn pexl_free_Match(m: *mut pexl_Match);
}
extern "C" {
  pub fn pexl_Match_failed(match_: *mut pexl_Match) -> bool;
}
extern "C" {
  pub fn pexl_Match_end(match_: *mut pexl_Match) -> pexl_Position;
}
extern "C" {
  pub fn pexl_MatchNode_start(node: *mut pexl_MatchNode) -> pexl_Position;
}
extern "C" {
  pub fn pexl_MatchNode_end(node: *mut pexl_MatchNode) -> pexl_Position;
}
extern "C" {
  pub fn pexl_MatchTree_iter(
    m: *mut pexl_Match,
    prev: pexl_Index,
    node: *mut *mut pexl_MatchNode,
  ) -> ::std::os::raw::c_int;
}
extern "C" {
  pub fn pexl_MatchTree_child(
    m: *mut pexl_Match,
    parent: pexl_Index,
    node: *mut *mut pexl_MatchNode,
  ) -> ::std::os::raw::c_int;
}
extern "C" {
  pub fn pexl_MatchTree_next(
    m: *mut pexl_Match,
    prev: pexl_Index,
    node: *mut *mut pexl_MatchNode,
  ) -> ::std::os::raw::c_int;
}
extern "C" {
  pub fn pexl_MatchTree_size(m: *mut pexl_Match) -> ::std::os::raw::c_int;
}
pub type pexl_Ref = pexl_Index;
extern "C" {
  pub fn pexl_Ref_notfound(r: pexl_Ref) -> bool;
}
extern "C" {
  pub fn pexl_Ref_invalid(r: pexl_Ref) -> bool;
}
pub type pexl_Error = u64;
extern "C" {
  pub fn pexl_Error_value(err: pexl_Error) -> pexl_Index;
}
extern "C" {
  pub fn pexl_Error_location(err: pexl_Error) -> pexl_Index;
}
pub type pexl_Env = pexl_Index;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_Stats {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_Optims {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_Binary {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_Context {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_Expr {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_PackageTable {
  _unused: [u8; 0],
}
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct pexl_BinaryAttributes {
  _unused: [u8; 0],
}
pub const pexl_OptimType_PEXL_OPT_SIMD: pexl_OptimType = 0;
pub const pexl_OptimType_PEXL_OPT_DYNAMIC_SIMD: pexl_OptimType = 1;
pub const pexl_OptimType_PEXL_OPT_INLINE: pexl_OptimType = 2;
pub const pexl_OptimType_PEXL_OPT_UNROLL: pexl_OptimType = 3;
pub const pexl_OptimType_PEXL_OPT_TRO: pexl_OptimType = 4;
pub const pexl_OptimType_PEXL_OPT_PEEPHOLE: pexl_OptimType = 5;
pub type pexl_OptimType = ::std::os::raw::c_uint;
pub const pexl_CharEncoding_PEXL_CHAR_ASCII: pexl_CharEncoding = 0;
pub const pexl_CharEncoding_PEXL_CHAR_UTF8: pexl_CharEncoding = 1;
pub type pexl_CharEncoding = ::std::os::raw::c_uint;
extern "C" {
  pub fn pexl_new_Context() -> *mut pexl_Context;
}
extern "C" {
  pub fn pexl_free_Context(C: *mut pexl_Context);
}
extern "C" {
  pub fn pexl_bind(
    C: *mut pexl_Context,
    exp: *mut pexl_Expr,
    name: *const ::std::os::raw::c_char,
  ) -> pexl_Ref;
}
extern "C" {
  pub fn pexl_bind_in(
    C: *mut pexl_Context,
    env: pexl_Env,
    exp: *mut pexl_Expr,
    name: *const ::std::os::raw::c_char,
  ) -> pexl_Ref;
}
extern "C" {
  pub fn pexl_rebind(
    C: *mut pexl_Context,
    ref_: pexl_Ref,
    exp: *mut pexl_Expr,
  ) -> ::std::os::raw::c_int;
}
extern "C" {
  pub fn pexl_compile(
    C: *mut pexl_Context,
    main: pexl_Ref,
    optims: *mut pexl_Optims,
    attrs: *mut pexl_BinaryAttributes,
    enc: pexl_CharEncoding,
    err: *mut pexl_Error,
  ) -> *mut pexl_Binary;
}
extern "C" {
  pub fn pexl_free_Binary(pkg: *mut pexl_Binary);
}
extern "C" {
  pub fn pexl_addopt_inline(optims: *mut pexl_Optims) -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_addopt_peephole(optims: *mut pexl_Optims) -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_addopt_unroll(optims: *mut pexl_Optims, max_times_to_unroll: u32)
    -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_addopt_tro(optims: *mut pexl_Optims) -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_addopt_simd(optims: *mut pexl_Optims, cache_size: u32) -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_addopt_dynamic_simd(optims: *mut pexl_Optims) -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_default_Optims() -> *mut pexl_Optims;
}
extern "C" {
  pub fn pexl_free_Optims(optims: *mut pexl_Optims);
}
extern "C" {
  pub fn pexl_scope_push(C: *mut pexl_Context) -> pexl_Env;
}
extern "C" {
  pub fn pexl_scope_pop(C: *mut pexl_Context) -> pexl_Env;
}
extern "C" {
  pub fn pexl_free_Expr(exp: *mut pexl_Expr);
}
extern "C" {
  pub fn pexl_copy_Expr(exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_bytes(
    C: *mut pexl_Context,
    ptr: *const ::std::os::raw::c_char,
    len: usize,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_string(
    C: *mut pexl_Context,
    str_: *const ::std::os::raw::c_char,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_epsilon(C: *mut pexl_Context) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_any(C: *mut pexl_Context, n: ::std::os::raw::c_int) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_set(
    C: *mut pexl_Context,
    set: *const ::std::os::raw::c_char,
    len: usize,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_complement(
    C: *mut pexl_Context,
    set: *const ::std::os::raw::c_char,
    len: usize,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_match_range(C: *mut pexl_Context, from: pexl_Byte, to: pexl_Byte) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_fail(C: *mut pexl_Context) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_seq(
    C: *mut pexl_Context,
    exp1: *mut pexl_Expr,
    exp2: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_seq_f(
    C: *mut pexl_Context,
    exp1: *mut pexl_Expr,
    exp2: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_choice(
    C: *mut pexl_Context,
    t1: *mut pexl_Expr,
    t2: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_choice_f(
    C: *mut pexl_Context,
    exp1: *mut pexl_Expr,
    exp2: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_repeat(
    C: *mut pexl_Context,
    tree: *mut pexl_Expr,
    min: pexl_Index,
    max: pexl_Index,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_repeat_f(
    C: *mut pexl_Context,
    exp: *mut pexl_Expr,
    min: pexl_Index,
    max: pexl_Index,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_lookahead(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_lookahead_f(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_neg_lookahead(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_neg_lookahead_f(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_lookbehind(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_lookbehind_f(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_neg_lookbehind(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_neg_lookbehind_f(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_call(C: *mut pexl_Context, ref_: pexl_Ref) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_xcall(C: *mut pexl_Context, pkg: *mut pexl_Binary, sym: pexl_Index)
    -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_capture(
    C: *mut pexl_Context,
    name: *const ::std::os::raw::c_char,
    tree1: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_capture_f(
    C: *mut pexl_Context,
    name: *const ::std::os::raw::c_char,
    exp: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_insert(
    C: *mut pexl_Context,
    name: *const ::std::os::raw::c_char,
    value: *const ::std::os::raw::c_char,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_find(Ctx: *mut pexl_Context, t1: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_find_f(C: *mut pexl_Context, exp: *mut pexl_Expr) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_backref(
    C: *mut pexl_Context,
    capname: *const ::std::os::raw::c_char,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_where(
    C: *mut pexl_Context,
    t1: *mut pexl_Expr,
    pathstring: *mut ::std::os::raw::c_char,
    t2: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_where_f(
    C: *mut pexl_Context,
    t1: *mut pexl_Expr,
    pathstring: *mut ::std::os::raw::c_char,
    t2: *mut pexl_Expr,
  ) -> *mut pexl_Expr;
}
extern "C" {
  pub fn pexl_binary_has_simd(p: *mut pexl_Binary) -> bool;
}
extern "C" {
  pub fn pexl_simd_available() -> bool;
}
extern "C" {
  pub fn pexl_run(
    pkg: *mut pexl_Binary,
    pt: *mut pexl_PackageTable,
    patname: *const ::std::os::raw::c_char,
    input: *const ::std::os::raw::c_char,
    inputlen: usize,
    start: usize,
    vm_flags: u32,
    stats: *mut pexl_Stats,
    match_: *mut pexl_Match,
  ) -> ::std::os::raw::c_int;
}
extern "C" {
  pub fn pexl_print_Env(env: pexl_Env, C: *mut pexl_Context);
}
extern "C" {
  pub fn pexl_print_Expr(tree: *mut pexl_Expr, indent: ::std::os::raw::c_int, C: *mut pexl_Context);
}
extern "C" {
  pub fn pexl_print_Binary(p: *mut pexl_Binary);
}
extern "C" {
  pub fn pexl_print_Match(match_: *mut pexl_Match);
}
extern "C" {
  pub fn pexl_print_Match_summary(match_: *mut pexl_Match);
}
extern "C" {
  pub fn pexl_print_Match_data(match_: *mut pexl_Match);
}

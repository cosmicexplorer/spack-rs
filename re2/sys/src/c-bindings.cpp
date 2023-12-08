/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#include "c-bindings.hpp"

#include <cassert>

namespace re2_c_bindings {
StringWrapper::StringWrapper(StringView s)
    : inner_(new std::string(s.data_, s.len_)) {}

void StringWrapper::clear() {
  delete inner_;
  inner_ = nullptr;
}

void StringWrapper::resize(const size_t len) {
  if (len == 0) {
    return clear();
  }
  get_mutable()->resize(len);
}

StringView StringWrapper::as_view() const {
  if (!inner_) {
    return StringView();
  }
  return StringView(inner_->data(), inner_->size());
}

StringMut StringWrapper::as_mut_view() {
  if (!inner_) {
    return StringMut();
  }
  return StringMut(inner_->data(), inner_->size());
}

void NamedCapturingGroups::deref(NamedGroup *out) const {
  out->name_ = absl::string_view(it_->second);
  assert(it_->first > 0);
  out->index_ = it_->first;
}

void NamedCapturingGroups::advance() { ++it_; }

bool NamedCapturingGroups::completed() const noexcept {
  return it_ == named_groups_.cend();
}

void RE2Wrapper::quote_meta(const StringView pattern, StringWrapper *out) {
  *out->get_mutable() =
      std::move(re2::RE2::QuoteMeta(pattern.into_absl_view()));
}

size_t RE2Wrapper::max_submatch(const StringView rewrite) {
  int ret = re2::RE2::MaxSubmatch(rewrite.into_absl_view());
  assert(ret >= 0);
  return ret;
}

RE2Wrapper::RE2Wrapper(StringView pattern, const re2::RE2::Options &options)
    : re_(new re2::RE2(pattern.into_absl_view(), options)) {}

void RE2Wrapper::clear() {
  delete re_;
  re_ = nullptr;
}

const re2::RE2::Options &RE2Wrapper::options() const noexcept {
  return re_->options();
}

re2::RE2::ErrorCode RE2Wrapper::error_code() const noexcept {
  return re_->error_code();
}

StringView RE2Wrapper::pattern() const noexcept {
  absl::string_view sv(re_->pattern());
  return StringView(sv);
}

StringView RE2Wrapper::error() const noexcept {
  absl::string_view sv(re_->error());
  return StringView(sv);
}

StringView RE2Wrapper::error_arg() const noexcept {
  absl::string_view sv(re_->error_arg());
  return StringView(sv);
}

size_t RE2Wrapper::num_captures() const noexcept {
  int n = re_->NumberOfCapturingGroups();
  assert(n >= 0);
  return n;
}

NamedCapturingGroups RE2Wrapper::named_groups() const {
  return NamedCapturingGroups(re_->CapturingGroupNames());
}

static bool parse_string_view(const char *data, size_t len, void *dest) {
  StringView *dest_sv = reinterpret_cast<StringView *>(dest);
  dest_sv->data_ = data;
  dest_sv->len_ = len;
  return true;
}

bool RE2Wrapper::full_match(const StringView text) const {
  return re2::RE2::FullMatchN(text.into_absl_view(), *re_, nullptr, 0);
}

bool RE2Wrapper::full_match_n(const StringView text, StringView captures[],
                              const size_t n) const {
  /* TODO: alloca only works on linux! */
  re2::RE2::Arg *argv =
      reinterpret_cast<re2::RE2::Arg *>(alloca(n * sizeof(re2::RE2::Arg)));
  re2::RE2::Arg **argv_ref =
      reinterpret_cast<re2::RE2::Arg **>(alloca(n * sizeof(re2::RE2::Arg *)));
  for (size_t i = 0; i < n; ++i) {
    StringView *capture_output = &captures[i];
    re2::RE2::Arg::Parser parser = parse_string_view;
    argv[i] = re2::RE2::Arg(capture_output, parser);
    argv_ref[i] = &argv[i];
  }

  return re2::RE2::FullMatchN(text.into_absl_view(), *re_, argv_ref, n);
}

bool RE2Wrapper::partial_match(const StringView text) const {
  return re2::RE2::PartialMatchN(text.into_absl_view(), *re_, nullptr, 0);
}

bool RE2Wrapper::partial_match_n(const StringView text, StringView captures[],
                                 const size_t n) const {
  /* TODO: alloca only works on linux! */
  re2::RE2::Arg *argv =
      reinterpret_cast<re2::RE2::Arg *>(alloca(n * sizeof(re2::RE2::Arg)));
  re2::RE2::Arg **argv_ref =
      reinterpret_cast<re2::RE2::Arg **>(alloca(n * sizeof(re2::RE2::Arg *)));
  for (size_t i = 0; i < n; ++i) {
    StringView *capture_output = &captures[i];
    re2::RE2::Arg::Parser parser = parse_string_view;
    argv[i] = re2::RE2::Arg(capture_output, parser);
    argv_ref[i] = &argv[i];
  }

  return re2::RE2::PartialMatchN(text.into_absl_view(), *re_, argv_ref, n);
}

class MutableStringViewInternal {
public:
  MutableStringViewInternal(StringView *text)
      : view_(text->into_absl_view()), handle_(text) {}

  absl::string_view *as_mutable() noexcept { return &view_; }

  /* Write the new value of the absl::string_view back into the FFI handle. */
  ~MutableStringViewInternal() { *handle_ = StringView(view_); }

private:
  absl::string_view view_;
  StringView *handle_;
};

bool RE2Wrapper::consume(StringView *text) const {
  MutableStringViewInternal tv(text);
  return re2::RE2::ConsumeN(tv.as_mutable(), *re_, nullptr, 0);
}

bool RE2Wrapper::consume_n(StringView *text, StringView captures[],
                           const size_t n) const {
  /* TODO: alloca only works on linux! */
  re2::RE2::Arg *argv =
      reinterpret_cast<re2::RE2::Arg *>(alloca(n * sizeof(re2::RE2::Arg)));
  re2::RE2::Arg **argv_ref =
      reinterpret_cast<re2::RE2::Arg **>(alloca(n * sizeof(re2::RE2::Arg *)));
  for (size_t i = 0; i < n; ++i) {
    StringView *capture_output = &captures[i];
    re2::RE2::Arg::Parser parser = parse_string_view;
    argv[i] = re2::RE2::Arg(capture_output, parser);
    argv_ref[i] = &argv[i];
  }

  MutableStringViewInternal tv(text);
  return re2::RE2::ConsumeN(tv.as_mutable(), *re_, argv_ref, n);
}

bool RE2Wrapper::find_and_consume(StringView *text) const {
  MutableStringViewInternal tv(text);
  return re2::RE2::FindAndConsumeN(tv.as_mutable(), *re_, nullptr, 0);
}

bool RE2Wrapper::find_and_consume_n(StringView *text, StringView captures[],
                                    const size_t n) const {
  /* TODO: alloca only works on linux! */
  re2::RE2::Arg *argv =
      reinterpret_cast<re2::RE2::Arg *>(alloca(n * sizeof(re2::RE2::Arg)));
  re2::RE2::Arg **argv_ref =
      reinterpret_cast<re2::RE2::Arg **>(alloca(n * sizeof(re2::RE2::Arg *)));
  for (size_t i = 0; i < n; ++i) {
    StringView *capture_output = &captures[i];
    re2::RE2::Arg::Parser parser = parse_string_view;
    argv[i] = re2::RE2::Arg(capture_output, parser);
    argv_ref[i] = &argv[i];
  }

  MutableStringViewInternal tv(text);
  return re2::RE2::FindAndConsumeN(tv.as_mutable(), *re_, argv_ref, n);
}

bool RE2Wrapper::replace(StringWrapper *inout, const StringView rewrite) const {
  return re2::RE2::Replace(inout->get_mutable(), *re_,
                           rewrite.into_absl_view());
}

size_t RE2Wrapper::global_replace(StringWrapper *inout,
                                  const StringView rewrite) const {
  int ret = re2::RE2::GlobalReplace(inout->get_mutable(), *re_,
                                    rewrite.into_absl_view());
  assert(ret >= 0);
  return ret;
}

bool RE2Wrapper::extract(const StringView text, const StringView rewrite,
                         StringWrapper *out) const {
  return re2::RE2::Extract(text.into_absl_view(), *re_,
                           rewrite.into_absl_view(), out->get_mutable());
}

bool RE2Wrapper::match_single(const StringView text, const size_t startpos,
                              const size_t endpos,
                              const re2::RE2::Anchor re_anchor) const {
  return re_->Match(text.into_absl_view(), startpos, endpos, re_anchor, nullptr,
                    0);
}

bool RE2Wrapper::match_routine(const StringView text, const size_t startpos,
                               const size_t endpos,
                               const re2::RE2::Anchor re_anchor,
                               StringView submatch_args[],
                               const size_t nsubmatch) const {
  /* TODO: alloca only works on linux! */
  absl::string_view *submatches = reinterpret_cast<absl::string_view *>(
      alloca(nsubmatch * sizeof(absl::string_view)));

  if (!re_->Match(text.into_absl_view(), startpos, endpos, re_anchor,
                  submatches, nsubmatch)) {
    return false;
  }

  for (size_t i = 0; i < nsubmatch; ++i) {
    submatch_args[i] = submatches[i];
  }
  return true;
}

bool RE2Wrapper::check_rewrite_string(const StringView rewrite,
                                      StringWrapper *error) const {
  return re_->CheckRewriteString(rewrite.into_absl_view(),
                                 error->get_mutable());
}

bool RE2Wrapper::vector_rewrite(StringWrapper *out, const StringView rewrite,
                                const StringView *vec,
                                const size_t veclen) const {
  /* TODO: alloca only works on linux! */
  absl::string_view *match_components = reinterpret_cast<absl::string_view *>(
      alloca(veclen * sizeof(absl::string_view)));

  for (size_t i = 0; i < veclen; ++i) {
    match_components[i] = vec[i].into_absl_view();
  }

  return re_->Rewrite(out->get_mutable(), rewrite.into_absl_view(),
                      match_components, veclen);
}

void MatchedSetInfo::clear() {
  delete matches_;
  matches_ = nullptr;
}

const int *MatchedSetInfo::data() const noexcept {
  return get_mutable()->data();
}

size_t MatchedSetInfo::size() const noexcept { return get_mutable()->size(); }

size_t MatchedSetInfo::capacity() const noexcept {
  return get_mutable()->capacity();
}

void MatchedSetInfo::reserve(const size_t to) { get_mutable()->reserve(to); }

void MatchedSetInfo::set_len(const size_t to) { get_mutable()->resize(to); }

SetWrapper::SetWrapper(const re2::RE2::Options &options,
                       re2::RE2::Anchor anchor)
    : set_(new re2::RE2::Set(options, anchor)) {}

void SetWrapper::clear() {
  delete set_;
  set_ = nullptr;
}

int SetWrapper::add(const StringView pattern, StringWrapper *error) {
  return set_->Add(pattern.into_absl_view(), error->get_mutable());
}

bool SetWrapper::compile() { return set_->Compile(); }

bool SetWrapper::match_routine(const StringView text, MatchedSetInfo *v) const {
  return set_->Match(text.into_absl_view(), v->get_mutable());
}

bool SetWrapper::match_routine_with_error(
    const StringView text, MatchedSetInfo *v,
    re2::RE2::Set::ErrorInfo *error_info) const {
  return set_->Match(text.into_absl_view(), v->get_mutable(), error_info);
}

void StringSet::clear() {
  delete strings_;
  strings_ = nullptr;
}

const StringWrapper *StringSet::cdata() const noexcept {
  return strings_->data();
}

StringWrapper *StringSet::data() noexcept { return strings_->data(); }

size_t StringSet::size() const noexcept { return strings_->size(); }

FilteredRE2Wrapper::FilteredRE2Wrapper() : inner_(new re2::FilteredRE2()) {}

FilteredRE2Wrapper::FilteredRE2Wrapper(int min_atom_len)
    : inner_(new re2::FilteredRE2(min_atom_len)) {}

void FilteredRE2Wrapper::clear() {
  delete inner_;
  inner_ = nullptr;
}

re2::RE2::ErrorCode FilteredRE2Wrapper::add(StringView pattern,
                                            const re2::RE2::Options &options,
                                            int *id) {
  return inner_->Add(pattern.into_absl_view(), options, id);
}

void FilteredRE2Wrapper::compile(StringSet *strings_to_match) {
  std::vector<std::string> args;
  inner_->Compile(&args);
  StringSet::from_result(std::move(args), strings_to_match);
}

int FilteredRE2Wrapper::slow_first_match(StringView text) const {
  return inner_->SlowFirstMatch(text.into_absl_view());
}

int FilteredRE2Wrapper::first_match(StringView text,
                                    const MatchedSetInfo &atoms) const {
  return inner_->FirstMatch(text.into_absl_view(), *atoms.get_mutable());
}

bool FilteredRE2Wrapper::all_matches(StringView text,
                                     const MatchedSetInfo &atoms,
                                     MatchedSetInfo *matching_regexps) const {
  return inner_->AllMatches(text.into_absl_view(), *atoms.get_mutable(),
                            matching_regexps->get_mutable());
}

} /* namespace re2_c_bindings */

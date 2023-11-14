/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#include "c-bindings.hpp"

#include <cassert>

namespace re2_c_bindings {
using re2_c_bindings::StringWrapper;

StringWrapper::StringWrapper() : inner_(nullptr) {}
StringWrapper::StringWrapper(StringView s)
    : inner_(new std::string(s.data_, s.len_)) {}

void StringWrapper::clear() {
  delete inner_;
  inner_ = nullptr;
}

StringView StringWrapper::as_view() const {
  if (inner_ == nullptr) {
    return StringView();
  }
  return StringView(inner_->data(), inner_->size());
}

void NamedCapturingGroups::deref(NamedGroup *out) const {
  assert(!completed());

  out->name_ = absl::string_view(it_->first);
  assert(it_->second > 0);
  out->index_ = it_->second;
}

void NamedCapturingGroups::advance() {
  assert(!completed());
  ++it_;
}

bool NamedCapturingGroups::completed() const noexcept {
  return it_ == named_groups_.end();
}

void RE2Wrapper::quote_meta(const StringView pattern, StringWrapper *out) {
  *out->get_mutable() =
      std::move(re2::RE2::QuoteMeta(pattern.into_absl_view()));
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
  return NamedCapturingGroups(re_->NamedCapturingGroups());
}

bool RE2Wrapper::full_match(const StringView text) const {
  return re2::RE2::FullMatchN(text.into_absl_view(), *re_, nullptr, 0);
}

static bool parse_string_view(const char *data, size_t len, void *dest) {
  StringView *dest_sv = reinterpret_cast<StringView *>(dest);
  dest_sv->data_ = data;
  dest_sv->len_ = len;
  return true;
}

static std::vector<re2::RE2::Arg *> generate_n_args(StringView captures[],
                                                    const size_t n) {
  std::vector<re2::RE2::Arg *> argv;

  for (size_t i = 0; i < n; ++i) {
    StringView *capture_output = &captures[i];
    re2::RE2::Arg::Parser parser = parse_string_view;
    const auto a = new re2::RE2::Arg(capture_output, parser);
    argv.push_back(a);
  }

  return argv;
}

static void free_n_args(std::vector<re2::RE2::Arg *> &&argv) {
  for (auto p : argv) {
    delete p;
  }
}

bool RE2Wrapper::full_match_n(const StringView text, StringView captures[],
                              const size_t n) const {
  auto argv = generate_n_args(captures, n);
  bool ret = re2::RE2::FullMatchN(text.into_absl_view(), *re_, argv.data(), n);
  free_n_args(std::move(argv));
  return ret;
}

bool RE2Wrapper::partial_match(const StringView text) const {
  return re2::RE2::PartialMatchN(text.into_absl_view(), *re_, nullptr, 0);
}

bool RE2Wrapper::partial_match_n(const StringView text, StringView captures[],
                                 const size_t n) const {
  auto argv = generate_n_args(captures, n);
  bool ret =
      re2::RE2::PartialMatchN(text.into_absl_view(), *re_, argv.data(), n);
  free_n_args(std::move(argv));
  return ret;
}

bool RE2Wrapper::consume(StringView *text) const {
  auto tv = text->into_absl_view();
  bool ret = re2::RE2::ConsumeN(&tv, *re_, nullptr, 0);
  *text = StringView(tv);
  return ret;
}

bool RE2Wrapper::consume_n(StringView *text, StringView captures[],
                           const size_t n) const {
  auto tv = text->into_absl_view();
  auto argv = generate_n_args(captures, n);
  bool ret = re2::RE2::ConsumeN(&tv, *re_, argv.data(), n);
  free_n_args(std::move(argv));
  *text = StringView(tv);
  return ret;
}

bool RE2Wrapper::find_and_consume(StringView *text) const {
  auto tv = text->into_absl_view();
  bool ret = re2::RE2::FindAndConsumeN(&tv, *re_, nullptr, 0);
  *text = StringView(tv);
  return ret;
}

bool RE2Wrapper::find_and_consume_n(StringView *text, StringView captures[],
                                    size_t n) const {
  auto tv = text->into_absl_view();
  auto argv = generate_n_args(captures, n);
  bool ret = re2::RE2::FindAndConsumeN(&tv, *re_, argv.data(), n);
  free_n_args(std::move(argv));
  *text = StringView(tv);
  return ret;
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

} /* namespace re2_c_bindings */

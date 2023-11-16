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
  assert(!completed());

  out->name_ = absl::string_view(it_->second);
  assert(it_->first > 0);
  out->index_ = it_->first;
}

void NamedCapturingGroups::advance() {
  assert(!completed());
  ++it_;
}

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

class CapturesInternal {
public:
  CapturesInternal(StringView captures[], const size_t n) : argv_(n) {
    for (size_t i = 0; i < n; ++i) {
      StringView *capture_output = &captures[i];
      re2::RE2::Arg::Parser parser = CapturesInternal::parse_string_view;
      argv_[i] = new re2::RE2::Arg(capture_output, parser);
    }
  }
  ~CapturesInternal() {
    for (auto p : argv_) {
      delete p;
    }
  }

  size_t size() const noexcept { return argv_.size(); }
  const re2::RE2::Arg *const *data() const noexcept { return argv_.data(); }

  /* TODO: enable the user to override this functionality to return false for a
   failed parse with a custom function like in our hyperscan wrapper! */
  static bool parse_string_view(const char *data, size_t len, void *dest) {
    StringView *dest_sv = reinterpret_cast<StringView *>(dest);
    dest_sv->data_ = data;
    dest_sv->len_ = len;
    return true;
  }

private:
  std::vector<re2::RE2::Arg *> argv_;
};

bool RE2Wrapper::full_match(const StringView text) const {
  return re2::RE2::FullMatchN(text.into_absl_view(), *re_, nullptr, 0);
}

bool RE2Wrapper::full_match_n(const StringView text, StringView captures[],
                              const size_t n) const {
  CapturesInternal argv(captures, n);
  return re2::RE2::FullMatchN(text.into_absl_view(), *re_, argv.data(),
                              argv.size());
}

bool RE2Wrapper::partial_match(const StringView text) const {
  return re2::RE2::PartialMatchN(text.into_absl_view(), *re_, nullptr, 0);
}

bool RE2Wrapper::partial_match_n(const StringView text, StringView captures[],
                                 const size_t n) const {
  CapturesInternal argv(captures, n);
  return re2::RE2::PartialMatchN(text.into_absl_view(), *re_, argv.data(),
                                 argv.size());
}

class MutableStringViewInternal {
public:
  MutableStringViewInternal(StringView *text)
      : view_(text->into_absl_view()), handle_(text) {}

  absl::string_view *as_mutable() noexcept { return &view_; }

  /* Write the new value of the absl::string_view into the provided FFI handle. */
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
  MutableStringViewInternal tv(text);
  CapturesInternal argv(captures, n);
  return re2::RE2::ConsumeN(tv.as_mutable(), *re_, argv.data(), argv.size());
}

bool RE2Wrapper::find_and_consume(StringView *text) const {
  MutableStringViewInternal tv(text);
  return re2::RE2::FindAndConsumeN(tv.as_mutable(), *re_, nullptr, 0);
}

bool RE2Wrapper::find_and_consume_n(StringView *text, StringView captures[],
                                    size_t n) const {
  MutableStringViewInternal tv(text);
  CapturesInternal argv(captures, n);
  return re2::RE2::FindAndConsumeN(tv.as_mutable(), *re_, argv.data(),
                                   argv.size());
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

bool RE2Wrapper::match_single(const StringView text, size_t startpos,
                              size_t endpos, re2::RE2::Anchor re_anchor) const {
  return re_->Match(text.into_absl_view(), startpos, endpos, re_anchor, nullptr,
                    0);
}

bool RE2Wrapper::match_routine(const StringView text, size_t startpos,
                               size_t endpos, re2::RE2::Anchor re_anchor,
                               StringView submatch_args[],
                               const size_t nsubmatch) const {
  std::vector<absl::string_view> submatches(nsubmatch);

  if (!re_->Match(text.into_absl_view(), startpos, endpos, re_anchor,
                  submatches.data(), submatches.size())) {
    return false;
  }

  for (size_t i = 0; i < submatches.size(); ++i) {
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
  std::vector<absl::string_view> match_components(veclen);

  for (size_t i = 0; i < veclen; ++i) {
    match_components[i] = vec[i].into_absl_view();
  }

  return re_->Rewrite(out->get_mutable(), rewrite.into_absl_view(),
                      match_components.data(), match_components.size());
}

} /* namespace re2_c_bindings */

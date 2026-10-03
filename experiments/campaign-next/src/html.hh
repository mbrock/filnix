#pragma once

#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

namespace campaign::html {

inline std::string escape(std::string_view value) {
  std::string out;
  out.reserve(value.size());
  for (char c : value) {
    switch (c) {
    case '&':
      out += "&amp;";
      break;
    case '<':
      out += "&lt;";
      break;
    case '>':
      out += "&gt;";
      break;
    case '"':
      out += "&quot;";
      break;
    case '\'':
      out += "&#39;";
      break;
    default:
      out += c;
    }
  }
  return out;
}

// Tagflow's block construction, without an AST or ambient coroutine state.
// Names are code-owned literals; every text/attribute value is escaped.
// Attributes must be provided before children; there is no raw-string API.
class Writer {
public:
  using Attributes =
      std::initializer_list<std::pair<std::string_view, std::string_view>>;

  void text(std::string_view value) { bytes_ += escape(value); }

  template <class Children>
  void tag(std::string_view name, Attributes attributes, Children children) {
    bytes_ += '<';
    bytes_ += name;
    for (auto [key, value] : attributes) {
      bytes_ += ' ';
      bytes_ += key;
      bytes_ += "=\"";
      bytes_ += escape(value);
      bytes_ += '"';
    }
    bytes_ += '>';
    children();
    bytes_ += "</";
    bytes_ += name;
    bytes_ += '>';
  }

  template <class Children> void tag(std::string_view name, Children children) {
    tag(name, {}, std::move(children));
  }

  std::string str() && { return std::move(bytes_); }

private:
  std::string bytes_;
};
} // namespace campaign::html

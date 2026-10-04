#include "web.hh"
#include "html.hh"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>

namespace campaign {
namespace {
using html::escape;
std::string text(const json &j, const char *key, std::string fallback = {}) {
  return j.contains(key) && j.at(key).is_string() &&
                 !j.at(key).get<std::string>().empty()
             ? j.at(key).get<std::string>()
             : fallback;
}
std::uint64_t number(const json &j, const char *key) {
  return j.contains(key) && j.at(key).is_number()
             ? j.at(key).get<std::uint64_t>()
             : 0;
}
std::string seconds(std::int64_t ns) {
  std::ostringstream s;
  s << std::fixed << std::setprecision(3) << double(ns) / 1e9;
  return s.str() + "s";
}
std::string url(std::string_view s) {
  constexpr char digits[] = "0123456789ABCDEF";
  std::string out;
  for (unsigned char c : s) {
    if (std::isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~')
      out += c;
    else {
      out += '%';
      out += digits[c >> 4];
      out += digits[c & 15];
    }
  }
  return out;
}
std::string query(const std::string &run, const std::string &activity = {}) {
  return "run=" + url(run) +
         (activity.empty() ? "" : "&activity=" + url(activity));
}
std::string display_text(std::string_view s) {
  std::string out;
  for (unsigned char c : s) {
    if (c < 32 && c != '\n' && c != '\r' && c != '\t')
      out += "\xef\xbf\xbd";
    else
      out += c;
  }
  return out;
}
std::string plain(std::string_view s) {
  std::string out;
  for (std::size_t i = 0; i < s.size(); ++i) {
    if (s[i] == '\x1b' && i + 1 < s.size() && s[i + 1] == '[') {
      auto end = s.find_first_not_of("0123456789;:", i + 2);
      if (end != std::string_view::npos && s[end] == 'm') {
        i = end;
        continue;
      }
    }
    out += s[i];
  }
  return out;
}
std::string span(std::int64_t ns) {
  if (ns <= 0)
    return "—";
  auto s = ns / 1000000000;
  auto two = [](std::int64_t v) {
    return (v < 10 ? "0" : "") + std::to_string(v);
  };
  if (s < 1)
    return "<1s";
  if (s < 60)
    return std::to_string(s) + "s";
  if (s < 3600)
    return std::to_string(s / 60) + "m " + two(s % 60) + "s";
  return std::to_string(s / 3600) + "h " + two(s / 60 % 60) + "m";
}
// Elapsed time as a clock: 0:50, 12:03, 1:02:03.
std::string clock(std::int64_t ns) {
  auto s = std::max<std::int64_t>(0, ns) / 1000000000;
  auto two = [](std::int64_t v) {
    return (v < 10 ? "0" : "") + std::to_string(v);
  };
  if (s >= 3600)
    return std::to_string(s / 3600) + ":" + two(s / 60 % 60) + ":" + two(s % 60);
  return std::to_string(s / 60) + ":" + two(s % 60);
}
// Phase durations keep a decimal below ten seconds, where it matters.
std::string brief(std::int64_t ns) {
  if (ns >= 0 && ns < 10000000000) {
    std::ostringstream s;
    s << std::fixed << std::setprecision(1) << double(ns) / 1e9 << "s";
    return s.str();
  }
  return span(ns);
}
std::string thousands(std::uint64_t n) {
  auto s = std::to_string(n);
  for (auto i = std::ptrdiff_t(s.size()) - 3; i > 0; i -= 3)
    s.insert(std::size_t(i), ",");
  return s;
}

// "ffmpeg-headless-x86_64-unknown-linux-gnufilc0-8.1.2" reads as
// ffmpeg-headless 8.1.2; the host platform is shown once, not per row.
struct Name {
  std::string name, version, platform;
};
Name parse_name(std::string full) {
  Name n;
  if (auto pos = full.find("-unknown-linux-"); pos != std::string::npos && pos) {
    auto begin = full.rfind('-', pos - 1);
    auto end = full.find('-', pos + 15);
    bool last = end == std::string::npos;
    if (begin != std::string::npos) {
      n.platform = full.substr(begin + 1, last ? end : end - begin - 1);
      full.erase(begin, last ? end : end - begin);
    } else if (!last) { // A wrapper named for its target: "x86_64-…-gnufilc0-pkg-config".
      n.platform = full.substr(0, end);
      full.erase(0, end + 1);
    }
  }
  // Fetched files (patches, scripts, tarballs) keep their whole name.
  for (auto file : {".patch", ".diff", ".sh", ".tar", ".zip", "?"})
    if (full.find(file) != std::string::npos) {
      n.name = full;
      return n;
    }
  for (std::size_t i = 0; i + 1 < full.size(); ++i)
    if (full[i] == '-' && std::isdigit(static_cast<unsigned char>(full[i + 1]))) {
      n.version = full.substr(i + 1);
      full.resize(i);
      break;
    }
  n.name = full;
  return n;
}
std::string drv_name(const std::string &drv) {
  auto base = drv.substr(drv.rfind('/') + 1);
  if (auto dash = base.find('-'); dash != std::string::npos)
    base.erase(0, dash + 1);
  if (base.ends_with(".drv"))
    base.resize(base.size() - 4);
  return base;
}
void package(html::Writer &h, const std::string &full) {
  auto n = parse_name(full);
  h.tag("span", {{"class", "pkg"}}, [&] { h.text(n.name); });
  if (!n.version.empty())
    h.tag("span", {{"class", "version"}}, [&] { h.text(n.version); });
}
std::string package(const std::string &full) {
  html::Writer h;
  package(h, full);
  return std::move(h).str();
}

// One top-level Nix error, reduced to the derivation and what happened to it.
struct Cause {
  std::string drv, what;
  std::uint64_t seq = 0;
  bool origin = false;
};
Cause read_cause(const std::string &message) {
  auto t = plain(message);
  Cause c;
  if (auto a = t.find("/nix/store/"); a != std::string::npos)
    if (auto b = t.find(".drv", a); b != std::string::npos)
      c.drv = t.substr(a, b + 4 - a);
  auto line = [&](std::size_t from) {
    auto end = t.find('\n', from);
    return t.substr(from, end == std::string::npos ? end : end - from);
  };
  if (auto p = t.find("timed out after"); p != std::string::npos)
    c.what = line(p), c.origin = true;
  else if (p = t.find("failed with exit code"); p != std::string::npos)
    c.what = line(p), c.origin = true;
  else if (p = t.find("Reason:"); p != std::string::npos)
    c.what = line(p + 7);
  else {
    c.what = line(0);
    if (c.what.starts_with("error:"))
      c.what.erase(0, 6);
  }
  auto first = c.what.find_first_not_of(" ");
  c.what.erase(0, first == std::string::npos ? c.what.size() : first);
  while (!c.what.empty() && std::string_view(" .;").find(c.what.back()) !=
                                std::string_view::npos)
    c.what.pop_back();
  return c;
}
std::string cause_line(const json &s) {
  auto hex_text = text(s, "cause_hex");
  if (hex_text.empty())
    return {};
  auto c = read_cause(unhex(hex_text));
  if (c.drv.empty())
    return c.what;
  auto n = parse_name(drv_name(c.drv));
  return n.name + (n.version.empty() ? "" : " " + n.version) + " " + c.what;
}

struct SGR {
  std::string foreground, background;
  bool bold = false, dim = false, italic = false, underline = false,
       strike = false, inverse = false;

  static std::string indexed(unsigned n) {
    if (n < 16)
      return "var(--ansi-" + std::to_string(n) + ")";
    if (n >= 232) {
      auto v = std::to_string(8 + (n - 232) * 10);
      return "rgb(" + v + "," + v + "," + v + ")";
    }
    n -= 16;
    auto cube = [](unsigned c) { return c ? 55 + c * 40 : 0; };
    return "rgb(" + std::to_string(cube(n / 36)) + "," +
           std::to_string(cube(n / 6 % 6)) + "," + std::to_string(cube(n % 6)) +
           ")";
  }
  static std::vector<unsigned> numbers(std::string_view s, char separator) {
    std::vector<unsigned> values;
    do {
      auto end = s.find(separator);
      auto part = s.substr(0, end);
      unsigned n = 0;
      if (!part.empty()) {
        auto r = std::from_chars(part.data(), part.data() + part.size(), n);
        if (r.ec != std::errc{} || r.ptr != part.data() + part.size())
          return {};
      }
      values.push_back(n);
      if (end == std::string_view::npos)
        break;
      s.remove_prefix(end + 1);
    } while (true);
    return values;
  }
  bool color(const std::vector<unsigned> &p, std::size_t &i, bool colon) {
    auto &dest = p[i] == 38 ? foreground : background;
    if (i + 2 >= p.size())
      return false;
    auto mode = p[++i];
    if (mode == 5 && p[i + 1] <= 255) {
      dest = indexed(p[++i]);
      return true;
    }
    if (mode != 2)
      return false;
    // Colon truecolor optionally carries a color-space field (empty or 0).
    if (colon && p.size() == 6) {
      if (p[++i] != 0)
        return false;
    }
    if (i + 3 >= p.size())
      return false;
    auto r = p[++i], g = p[++i], b = p[++i];
    if (r > 255 || g > 255 || b > 255)
      return false;
    dest = "rgb(" + std::to_string(r) + "," + std::to_string(g) + "," +
           std::to_string(b) + ")";
    return true;
  }
  bool apply(std::string_view params) {
    if (params.find(':') != std::string_view::npos) {
      // A colon parameter is one group, even when mixed with semicolons.
      while (true) {
        auto colon = params.find(':');
        if (colon == std::string_view::npos)
          return apply(params);
        auto begin = params.rfind(';', colon);
        if (begin != std::string_view::npos && !apply(params.substr(0, begin)))
          return false;
        begin = begin == std::string_view::npos ? 0 : begin + 1;
        auto end = params.find(';', colon);
        auto group = params.substr(
            begin, end == std::string_view::npos ? end : end - begin);
        auto p = numbers(group, ':');
        std::size_t i = 0;
        if (p.empty() || (p[0] != 38 && p[0] != 48) || !color(p, i, true) ||
            i + 1 != p.size())
          return false;
        if (end == std::string_view::npos)
          return true;
        params.remove_prefix(end + 1);
      }
    }
    auto p = numbers(params, ';');
    if (p.empty())
      return false;
    for (std::size_t i = 0; i < p.size(); ++i) {
      auto n = p[i];
      if (n == 0)
        *this = {};
      else if (n == 1)
        bold = true;
      else if (n == 2)
        dim = true;
      else if (n == 3)
        italic = true;
      else if (n == 4)
        underline = true;
      else if (n == 7)
        inverse = true;
      else if (n == 9)
        strike = true;
      else if (n == 22)
        bold = dim = false;
      else if (n == 23)
        italic = false;
      else if (n == 24)
        underline = false;
      else if (n == 27)
        inverse = false;
      else if (n == 29)
        strike = false;
      else if (n >= 30 && n <= 37)
        foreground = indexed(n - 30);
      else if (n >= 40 && n <= 47)
        background = indexed(n - 40);
      else if (n >= 90 && n <= 97)
        foreground = indexed(n - 90 + 8);
      else if (n >= 100 && n <= 107)
        background = indexed(n - 100 + 8);
      else if (n == 39)
        foreground.clear();
      else if (n == 49)
        background.clear();
      else if (n == 38 || n == 48) {
        if (!color(p, i, false))
          return false;
      } else
        return false; // Unsupported SGR stays visible, not silently lost.
    }
    return true;
  }
  std::string css() const {
    auto fg = foreground, bg = background;
    if (inverse) {
      fg = background.empty() ? "var(--paper)" : background;
      bg = foreground.empty() ? "var(--ink)" : foreground;
    }
    std::string out;
    if (!fg.empty())
      out += "color:" + fg + ";";
    if (!bg.empty())
      out += "background-color:" + bg + ";";
    if (bold)
      out += "font-weight:700;";
    if (dim)
      out += "opacity:.7;";
    if (italic)
      out += "font-style:italic;";
    if (underline || strike)
      out += "text-decoration:" + std::string(underline ? "underline " : "") +
             (strike ? "line-through" : "") + ";";
    return out;
  }
};

std::string terminal(const std::string &hex_bytes) {
  auto s =
      json::parse(json(unhex(hex_bytes))
                      .dump(-1, ' ', false, json::error_handler_t::replace))
          .get<std::string>();
  html::Writer out;
  SGR style;
  auto emit = [&](std::string_view bytes) {
    if (bytes.empty())
      return;
    auto css = style.css();
    if (css.empty())
      out.text(display_text(bytes));
    else
      out.tag("span", {{"style", css}}, [&] { out.text(display_text(bytes)); });
  };
  std::size_t start = 0;
  for (std::size_t i = 0; i + 1 < s.size(); ++i) {
    if (s[i] != '\x1b' || s[i + 1] != '[')
      continue;
    auto end = s.find_first_not_of("0123456789;:", i + 2);
    if (end == std::string::npos || s[end] != 'm')
      continue;
    auto next = style;
    if (!next.apply(std::string_view(s).substr(i + 2, end - i - 2)))
      continue;
    emit(std::string_view(s).substr(start, i - start));
    style = std::move(next);
    start = end + 1;
    i = end;
  }
  emit(std::string_view(s).substr(start));
  return std::move(out).str();
}
const json *session(const json &view, const std::string &run) {
  if (view.contains("session") && view.at("session").is_object())
    return &view.at("session");
  for (const auto &s : view.at("sessions"))
    if (run.empty() || text(s, "run") == run)
      return &s;
  return nullptr;
}
std::string status(const json &view, const json &s) {
  if (!s.value("complete", false)) {
    if (text(s, "run") == text(view, "live_run") ||
        (view.value("live", false) && view.at("session").is_object() &&
         s.at("run") == view.at("session").at("run")))
      return "observing";
    return "incomplete";
  }
  auto result = text(s, "outcome", "incomplete");
  if (result == "substituted" || result == "resolves-to-already-valid")
    return "already-valid";
  if (result == "cancelled")
    return "interrupted";
  if (result == "worker-error" || result == "recorder-error")
    return "failed";
  return result;
}
std::string caption(const std::string &s) {
  if (s == "already-valid")
    return "already valid";
  if (s == "timed-out")
    return "timed out";
  if (s == "unattempted")
    return "not attempted";
  return s;
}
std::string badge(const std::string &s) {
  return "<span class=\"status\" data-status=\"" + escape(s) + "\">" +
         escape(caption(s)) + "</span>";
}
std::string lower(std::string s) {
  for (auto &c : s)
    c = std::tolower(static_cast<unsigned char>(c));
  return s;
}
std::string label(const json &s) {
  return text(s, "name", text(s, "drv", "Unknown derivation"));
}

// The recorded top-level errors in order, ending with the selected root:
// the derivation that broke first, then each one that could not build.
std::vector<Cause> causes(const json &v, const json &s) {
  std::vector<Cause> out;
  auto errors = v.value("reported_errors", json::array());
  for (auto it = errors.rbegin(); it != errors.rend(); ++it) {
    auto c = read_cause(unhex(text(*it, "bytes_hex")));
    c.seq = number(*it, "seq");
    if (!c.drv.empty())
      out.push_back(std::move(c));
  }
  auto root = text(s, "drv");
  if (!out.empty() && out.back().drv != root)
    for (const auto &e : v.value("failure_events", json::array()))
      if (e.at("payload").contains("result")) {
        auto c = read_cause(
            text(e.at("payload").at("result"), "errorMsg", "build failed"));
        c.drv = root;
        out.push_back(std::move(c));
        break;
      }
  return out;
}

struct Graph {
  struct Row {
    std::string drv, outputs;
    std::size_t depth;
    bool reference, dynamic;
  };
  const json &view;
  std::string run, root;
  std::map<std::string, const json *> recipes, activities;
  std::map<std::string, std::vector<const json *>> edges;
  std::map<std::string, std::string> direct_outputs;
  std::set<std::string> primary, reachable, failed;
  std::vector<Row> rows;
  Graph(const json &v, const json &s)
      : view(v), run(text(s, "run")), root(text(s, "drv")) {
    for (const auto &c : causes(v, s))
      failed.insert(c.drv);
    for (const auto &r : v.at("recipes"))
      recipes[text(r, "drv")] = &r;
    for (const auto &a : v.at("activities"))
      if (!text(a, "drv").empty())
        activities[text(a, "drv")] = &a;
    for (const auto &e : v.at("edges"))
      edges[text(e, "parent_drv")].push_back(&e);
    for (auto &[drv, children] : edges)
      std::sort(children.begin(), children.end(), [&](auto a, auto b) {
        return name(text(*a, "child_drv")) < name(text(*b, "child_drv"));
      });
    primary.insert(root);
    for (auto e : edges[root]) {
      auto drv = text(*e, "child_drv"), n = name(drv);
      bool bootstrap = n.starts_with("bash-") || n.starts_with("hex0-") ||
                       n.starts_with("hex1-") || n.starts_with("hex2-") ||
                       n.starts_with("kaem-") || n.starts_with("stage0-") ||
                       n.ends_with(".tar.gz") || n.ends_with(".tar.xz");
      if (!e->value("dynamic", false) && !bootstrap)
        primary.insert(drv);
    }
    std::vector<Row> pending{{root, "", 0, false, false}};
    while (!pending.empty()) {
      auto row = pending.back();
      pending.pop_back();
      if (row.depth == 1)
        direct_outputs[row.drv] = row.outputs;
      row.reference = !reachable.insert(row.drv).second;
      if (row.drv != root || row.reference)
        rows.push_back(row);
      if (row.reference || row.dynamic)
        continue;
      auto &children = edges[row.drv];
      for (auto it = children.rbegin(); it != children.rend(); ++it) {
        const auto &e = **it;
        std::string outputs;
        for (const auto &o : e.at("outputs")) {
          if (!outputs.empty())
            outputs += ", ";
          outputs += o.get<std::string>();
        }
        pending.push_back({text(e, "child_drv"), outputs, row.depth + 1, false,
                           e.value("dynamic", false)});
      }
    }
    for (auto &[drv, a] : activities)
      if (reachable.contains(drv) && text(*a, "status") == "running" &&
          v.value("live", false))
        primary.insert(drv);
  }
  std::string name(const std::string &drv) const {
    auto it = recipes.find(drv);
    return it == recipes.end() ? drv : label(*it->second);
  }
  std::string node(const Row &r, bool initial = false) const {
    auto anchor = "drv-" + hex(r.drv);
    bool reference = r.reference || (!initial && primary.contains(r.drv));
    auto full = name(r.drv);
    // Build-platform tools carry no host triple; they recede behind Fil-C
    // packages, which are what the campaign is about.
    // Build-platform tools carry no host triple; they are greyed so that a
    // tool and its Fil-C counterpart with the same name stay distinct.
    auto kind = std::string("graph-node") +
                (parse_name(full).platform.empty() ? " native" : "") +
                (failed.contains(r.drv) ? " failed" : "");
    std::string out = "<div class=\"" + kind + "\" data-name=\"" +
                      escape(full) + "\" title=\"" + escape(full) + "\"" +
                      (reference ? "" : " id=\"" + anchor + "\"") +
                      " style=\"--depth:" + std::to_string(r.depth) + "\">";
    out += "<a href=\"#" + anchor + "\" class=\"node-name\">" +
           (reference ? "<span class=\"ref\">reference</span>" : "") + package(full) +
           "</a>";
    if (r.drv == root)
      out += " " + badge(status(view, *session(view, run)));
    auto a = activities.find(r.drv);
    if (a != activities.end()) {
      auto &item = *a->second;
      auto start = item.value("start_elapsed_ns", std::int64_t(0));
      auto end = item.at("stop_elapsed_ns").is_number()
                     ? item.at("stop_elapsed_ns").get<std::int64_t>()
                     : view.value("elapsed_now_ns", std::int64_t(0));
      auto state = text(item, "status"), machine = text(item, "machine");
      std::string where =
          machine.empty() || machine == "local" ? "" : " on " + machine;
      // Built in this session; a live build names its current phase.
      std::string what =
          state != "running" ? "built"
          : view.value("live", false)
              ? text(item, "phase", "building")
              : "last seen in " + text(item, "phase", "build");
      out += "<span class=\"node-activity\">" + escape(what + where) + " " +
             escape(span(std::max<std::int64_t>(1, end - start))) +
             "</span><a class=\"node-output\" href=\"./?" +
             escape(query(run, text(item, "id"))) + "\">log</a>";
    }
    const auto &outputs =
        initial && r.drv != root && direct_outputs.contains(r.drv)
            ? direct_outputs.at(r.drv)
            : r.outputs;
    if (!outputs.empty() && outputs != "out")
      out += "<span>outputs · " + escape(outputs) + "</span>";
    if (r.dynamic)
      out += "<span>unknown dynamic dependency</span>";
    if (!recipes.contains(r.drv))
      out += "<span>recipe metadata unavailable</span>";
    return out + "</div>";
  }
};

std::string failure(const json &view, const json &s, const std::string &state) {
  if (state != "failed" && state != "timed-out" && state != "interrupted")
    return {};
  auto chain = causes(view, s);
  std::string out = "<section class=\"failure\" data-status=\"" +
                    escape(state) + "\"><h2>" +
                    (state == "failed" ? "Why it failed" : "Why it stopped") +
                    "</h2>";
  if (chain.size() > 1 || (chain.size() == 1 && chain[0].drv != text(s, "drv"))) {
    out += "<ol class=\"cause-chain\">";
    for (const auto &c : chain) {
      out += std::string("<li class=\"cause") + (c.origin ? " origin" : "") +
             "\" title=\"" + escape(c.drv) + "\">" +
             package(c.drv == text(s, "drv") ? label(s) : drv_name(c.drv)) +
             "<span class=\"cause-what\">" + escape(c.what) + "</span>";
      if (c.seq)
        out += "<button data-phase-seq=\"" + std::to_string(c.seq) +
               "\" data-phase-activity=\"\">Show in log</button>";
      out += "</li>";
    }
    return out + "</ol></section>";
  }
  std::string reason;
  for (const auto &e : view.value("failure_events", json::array())) {
    const auto &p = e.at("payload");
    auto kind = text(e, "kind");
    if (kind == "run.limit-reached") {
      reason = "root time limit reached";
      break;
    }
    if (kind == "run.cancel-requested") {
      reason = "signal " + std::to_string(number(p, "signal"));
      break;
    }
    if (p.contains("text_hex")) {
      reason = unhex(text(p, "text_hex"));
      break;
    }
    if (p.contains("result"))
      reason = text(p.at("result"), "errorMsg", p.at("result").dump());
  }
  if (auto paths = reason.find("Output paths:"); paths != std::string::npos)
    reason.resize(paths);
  if (auto why = reason.find("Reason:"); why != std::string::npos)
    reason.erase(0, why + 7);
  out += "<p class=\"cause-what\">" +
         terminal(hex(reason.empty() ? "no recorded reason" : reason)) + "</p>";
  auto phase = display_text(unhex(text(s, "phase_hex")));
  std::string context;
  if (!phase.empty())
    context += "during " + phase;
  if (auto d = std::int64_t(number(s, "duration_ns")); d > 0)
    context += (context.empty() ? "after " : " · after ") + span(d);
  if (!context.empty())
    out += "<p class=\"cause-context\">" + escape(context) + "</p>";
  return out + "</section>";
}

std::string phase_ledger(const json &v, const json &s) {
  const json *activity = nullptr;
  for (const auto &a : v.at("activities"))
    if (text(a, "drv") == text(s, "drv"))
      activity = &a;
  std::vector<const json *> phases;
  if (activity)
    for (const auto &p : v.at("phases"))
      if (text(p, "activity") == text(*activity, "id") &&
          (phases.empty() || text(*phases.back(), "phase") != text(p, "phase")))
        phases.push_back(&p);
  // A root that never ran its own builder has no phases; say nothing.
  if (phases.empty())
    return {};
  auto machine = text(*activity, "machine", "local");
  std::string out = "<section class=\"phase-ledger\"><h2>Phases" +
                    (machine == "local" ? "" : " · " + escape(machine)) +
                    "</h2><table><tbody>";
  std::int64_t total = 0;
  {
    auto first = phases.front()->at("elapsed_ns").get<std::int64_t>();
    auto stop = activity->at("stop_elapsed_ns");
    total = (stop.is_number() ? stop.get<std::int64_t>()
                              : v.value("elapsed_now_ns", first)) -
            first;
  }
  for (std::size_t i = 0; i < phases.size(); ++i) {
    const auto &p = *phases[i];
    auto start = p.at("elapsed_ns").get<std::int64_t>();
    auto end = i + 1 < phases.size() ? phases[i + 1]->at("elapsed_ns")
                                     : activity->at("stop_elapsed_ns");
    bool running = end.is_null() && v.value("live", false) &&
                   text(*activity, "status") == "running";
    if (running)
      end = v.at("elapsed_now_ns");
    auto duration = end.is_number() && end.get<std::int64_t>() >= start
                        ? brief(end.get<std::int64_t>() - start) +
                              (running ? " · running" : "")
                        : "— · end unobserved";
    std::string share = "0";
    if (total > 0 && end.is_number() && end.get<std::int64_t>() >= start)
      share = std::to_string(
          std::clamp<std::int64_t>((end.get<std::int64_t>() - start) * 1000 /
                                       total,
                                   0, 1000));
    out += "<tr><td><button data-phase-seq=\"" +
           std::to_string(number(p, "seq")) + "\" data-phase-activity=\"" +
           escape(text(p, "activity")) + "\">" + escape(text(p, "phase")) +
           "</button></td><td>" + duration +
           "</td><td><span class=\"phase-bar\" style=\"--share:" + share +
           "\"></span></td></tr>";
  }
  return out + "</tbody></table></section>";
}

// The source label is repeated per row; the client shows it only when it
// changes, so a single-derivation log reads as plain output.
std::string log_row(const json &r) {
  auto source = parse_name(text(r, "activity_name")).name;
  auto elapsed = r.value("elapsed_ns", std::int64_t(0));
  return "<div class=\"log-row\" data-seq=\"" +
         std::to_string(number(r, "seq")) + "\" data-source=\"" +
         escape(source) + "\"><span class=\"log-source\">" +
         escape(source.empty() ? "nix" : source) + "</span><time title=\"" +
         seconds(elapsed) + "\">" + clock(elapsed) + "</time><pre>" +
         terminal(text(r, "bytes_hex")) + "</pre></div>";
}
std::string earlier(const json &records, std::size_t window) {
  auto first = records.empty() ? 0 : number(records[0], "seq");
  bool more = window && records.size() >= window && first > 1;
  return "<button id=\"log-earlier\" data-first=\"" + std::to_string(first) +
         "\"" + (more ? "" : " hidden") + ">Load earlier output</button>";
}
bool watching(const json &v) {
  return v.value("watch", v.value("live", false));
}
std::string controls(const json &v) {
  std::string out =
      "<form id=\"rail-controls\" hx-get=\"./sessions\" "
      "hx-target=\"#session-results\" hx-trigger=\"change, submit" +
      std::string(watching(v) ? ", every 3s" : "") +
      "\"><input type=\"hidden\" id=\"rail-after\" name=\"after\" "
      "value=\"0\"><label>Filter <select name=\"filter\" "
      "id=\"session-filter\">";
  for (std::string s :
       {"all", "observing", "built", "already-valid", "incomplete", "failed",
        "interrupted", "timed-out", "successful", "unattempted"})
    out += "<option value=\"" + s + "\">" + caption(s) + "</option>";
  out += "</select></label><label>Find <input name=\"find\" "
         "id=\"session-find\" type=\"search\" "
         "placeholder=\"Package name\"></label></form>";
  return out;
}
// Counts as a proportional bar plus filter chips, in severity order.
std::string campaign_line(const json &v) {
  if (!v.contains("cohort") || !v.at("cohort").is_object())
    return {};
  const auto &c = v.at("cohort");
  auto total = c.at("roots").size();
  auto running = number(c, "attempted") - number(c, "completed");
  std::vector<std::tuple<std::string, std::uint64_t, std::string>> parts{
      {"failed", number(c, "failed"), "failed"},
      {"timed-out", number(c, "timed_out"), "timed out"},
      {"observing", running, "building"},
      {"built", number(c, "built"), "built"},
      {"already-valid", number(c, "already_valid"), "already valid"},
      {"unattempted", number(c, "unattempted"), "not attempted"}};
  std::string bar = "<div class=\"tally-bar\" role=\"img\" aria-label=\"" +
                    std::to_string(number(c, "completed")) + " of " +
                    std::to_string(total) + " roots settled\">";
  std::string chips = "<div class=\"campaign-line\">";
  for (const auto &[filter, n, label] : parts) {
    if (n)
      bar += "<span data-status=\"" + filter + "\" style=\"flex:" +
             std::to_string(n) + "\" title=\"" + std::to_string(n) + " " +
             label + "\"></span>";
    if (n || filter == "failed" || filter == "built")
      chips += "<button class=\"chip\" data-filter=\"" + filter +
               "\" data-status=\"" + filter + "\"><b>" + std::to_string(n) +
               "</b> " + label + "</button>";
  }
  return bar + "</div>" + chips + "</div>";
}

} // namespace

std::string web_sessions(const json &v, const std::string &run,
                         const std::string &filter, const std::string &find,
                         std::uint64_t after) {
  std::vector<json> matches;
  std::set<std::uint64_t> attempted;
  auto cohort = v.value("cohort", json(nullptr));
  for (const auto &s : v.at("sessions")) {
    auto request = s.value("request", json(nullptr));
    if (cohort.is_object()) {
      if (!request.is_object() || !request.contains("cohort") ||
          request.at("cohort").at("id") != cohort.at("id"))
        continue;
      attempted.insert(number(request, "index"));
    }
    auto st = status(v, s);
    bool pass =
        filter.empty() || filter == "all" || filter == st ||
        (filter == "failed" && st == "interrupted") ||
        (filter == "successful" && (st == "built" || st == "already-valid"));
    if (pass && lower(label(s)).find(lower(find)) != std::string::npos)
      matches.push_back(s);
  }
  if ((filter == "unattempted" || filter.empty() || filter == "all") &&
      cohort.is_object()) {
    for (std::size_t i = 0; i < cohort.at("roots").size(); ++i)
      if (!attempted.contains(i) &&
          lower(label(cohort.at("roots")[i])).find(lower(find)) !=
              std::string::npos)
        matches.push_back(cohort.at("roots")[i]);
  }
  // Problems first, then work in progress, builds, cached and unattempted
  // roots; recording order (latest first) within each group.
  auto rank = [&](const json &s) {
    auto st = text(s, "run").empty() ? "unattempted" : status(v, s);
    for (int i = 0; auto group : {"failed", "interrupted", "timed-out",
                                  "incomplete", "observing", "built",
                                  "already-valid"}) {
      if (st == group)
        return i;
      ++i;
    }
    return 7;
  };
  std::stable_sort(matches.begin(), matches.end(),
                   [&](const json &a, const json &b) { return rank(a) < rank(b); });
  constexpr std::uint64_t window = 100;
  after = std::min<std::uint64_t>(after, matches.size());
  std::string out = "<p class=\"rail-count\" data-after=\"" +
                    std::to_string(after) + "\">" +
                    std::to_string(matches.size()) +
                    (cohort.is_object() ? " roots</p>" : " sessions</p>");
  auto end = std::min<std::uint64_t>(matches.size(), after + window);
  {
    html::Writer h;
    h.tag("table", {{"class", "campaign-table"}}, [&] {
      h.tag("thead", [&] {
        h.tag("tr", [&] {
          for (auto name :
               {"Package", "Version", "Status", "Duration", "Detail"})
            h.tag("th", {{"scope", "col"}}, [&] { h.text(name); });
        });
      });
      h.tag("tbody", [&] {
        for (auto i = after; i < end; ++i) {
          const auto &s = matches[i];
          auto id = text(s, "run"),
               st = id.empty() ? "unattempted" : status(v, s);
          auto n = parse_name(label(s));
          h.tag("tr", {{"data-status", st}}, [&] {
            h.tag("td", {{"class", "pkg-cell"}, {"title", label(s)}}, [&] {
              if (id.empty())
                h.text(n.name);
              else {
                auto href = "./?" + query(id) + "&filter=" + url(filter) +
                            "&find=" + url(find);
                h.tag("a", {{"href", href}}, [&] { h.text(n.name); });
              }
            });
            h.tag("td", {{"class", "version"}}, [&] { h.text(n.version); });
            h.tag("td", [&] {
              h.tag("span", {{"class", "status"}, {"data-status", st}},
                    [&] { h.text(caption(st)); });
            });
            h.tag("td", {{"class", "duration"}}, [&] {
              h.text(id.empty() ? "" : span(std::int64_t(number(s, "duration_ns"))));
            });
            // Only problems and live work carry a detail; success needs none.
            h.tag("td", {{"class", "session-observation"}}, [&] {
              auto phase = display_text(unhex(text(s, "phase_hex")));
              if (st == "failed" || st == "interrupted")
                h.text(cause_line(s).empty() ? text(s, "native_status")
                                             : cause_line(s));
              else if (st == "timed-out")
                h.text("time limit reached" +
                       (phase.empty() ? "" : " in " + phase));
              else if (st == "observing" || st == "incomplete")
                h.text(phase);
            });
          });
        }
      });
    });
    out += std::move(h).str();
  }
  if (matches.empty())
    out += "<p class=\"empty\">No sessions · " +
           escape(filter.empty() ? "all" : filter) + "</p>";
  auto page = [&](std::uint64_t offset, const std::string &caption) {
    return "<button hx-get=\"./sessions?" + escape(query(run)) +
           "&amp;filter=" + escape(url(filter)) +
           "&amp;find=" + escape(url(find)) +
           "&amp;after=" + std::to_string(offset) +
           "\" hx-target=\"#session-results\">" + caption + "</button>";
  };
  out += "<div class=\"paging\">";
  if (after)
    out += page(after >= window ? after - window : 0, "Previous 100");
  if (end < matches.size())
    out += page(end, "Show next 100");
  return out + "</div>";
}

std::string web_graph(const json &v, const std::string &run,
                      std::uint64_t after, const std::string &node) {
  auto s = session(v, run);
  if (!s)
    return "<p>No recorded graph.</p>";
  Graph g(v, *s);
  if (!node.empty())
    for (std::size_t i = 0; i < g.rows.size(); ++i)
      if (g.rows[i].drv == node && !g.rows[i].reference) {
        after = i / 500 * 500;
        break;
      }
  after = std::min<std::uint64_t>(after, g.rows.size());
  auto end = std::min<std::uint64_t>(g.rows.size(), after + 500);
  std::string out = "<p class=\"snapshot\">Snapshot · " +
                    std::to_string(number(v, "watermark")) + " · " +
                    std::to_string(after) + "–" + std::to_string(end) + " / " +
                    std::to_string(g.rows.size()) + " rows</p>";
  for (auto i = after; i < end; ++i)
    out += g.node(g.rows[i]);
  auto page = [&](std::uint64_t offset, const std::string &caption) {
    return "<button hx-get=\"./graph?" + escape(query(g.run)) +
           "&amp;after=" + std::to_string(offset) +
           "\" hx-target=\"#static-rows\">" + caption + "</button>";
  };
  out += "<div class=\"paging\">";
  if (after)
    out += page(after >= 500 ? after - 500 : 0, "Previous 500");
  if (end < g.rows.size())
    out += "<span class=\"graph-truncated\">Remaining dependencies omitted "
           "(500-node limit).</span>" +
           page(end, "Show next 500");
  return out + "</div>";
}

std::string web_state(const json &v, const std::string &run,
                      const std::string &activity) {
  auto s = session(v, run);
  auto id = s ? text(*s, "run") : run;
  std::string out =
      "<section id=\"state\" data-run=\"" + escape(id) + "\" data-live=\"" +
      (v.value("live", false) ? "1" : "0") + "\" data-watch=\"" +
      (watching(v) ? "1" : "0") + "\" hx-get=\"./state?" +
      escape(query(run, activity)) + "\" hx-trigger=\"refresh" +
      (watching(v) ? ", every 2s" : "") + "\" hx-swap=\"outerHTML\">";
  if (!s)
    return out + "<h1>No recorded session</h1></section>";
  auto st = status(v, *s);
  Graph g(v, *s);
  auto count = g.reachable.size() - g.primary.size();
  auto platform = parse_name(label(*s)).platform;
  out += "<header class=\"summary-head\"><h1 title=\"" + escape(label(*s)) +
         "\">" + package(label(*s)) + "</h1><div class=\"head-meta\">" +
         badge(st) +
         (platform.empty() ? ""
                           : " <span class=\"platform\">" + escape(platform) +
                                 "</span>") +
         " <span class=\"record-mode\" data-live=\"" +
         (v.value("live", false) ? "1\">Live" : "0\">Recorded") +
         "</span></div></header>" + failure(v, *s, st) +
         "<div id=\"inspection-scroll\" role=\"region\" "
         "aria-label=\"Session inspector\">";
  out += "<dl class=\"facts\"><div class=\"drv-fact\"><dt>DERIVATION <button "
         "data-copy=\"" +
         escape(text(*s, "drv")) +
         "\">Copy drv</button></dt><dd class=\"root-anchor\" id=\"drv-" +
         hex(g.root) + "\" data-name=\"" + escape(label(*s)) + "\">" +
         escape(text(*s, "drv", "—")) + "</dd></div>";
  for (auto &[caption, value] :
       std::vector<std::pair<std::string, std::string>>{
           {"SYSTEM", text(*s, "system", "—")},
           {"DURATION", span(std::int64_t(number(*s, "duration_ns")))},
           {"LOG LINES", thousands(number(*s, "output_lines"))}})
    out += "<div><dt>" + caption + "</dt><dd>" + escape(value) + "</dd></div>";
  out += "</dl>";
  if (!v.value("reported_errors", json::array()).empty()) {
    out += "<details class=\"reported-errors\"><summary>Reported errors · " +
           std::to_string(v.at("reported_errors").size()) + "</summary>";
    for (const auto &e : v.at("reported_errors"))
      out += "<button data-phase-seq=\"" + std::to_string(number(e, "seq")) +
             "\" data-phase-activity=\"\">Show in log · " +
             clock(e.at("elapsed_ns").get<std::int64_t>()) +
             "</button><pre>" + terminal(text(e, "bytes_hex")) + "</pre>";
    out += "</details>";
  }
  std::string paths;
  for (const auto &o : s->value("outputs", json::array()))
    paths += text(o, "path") + "\n";
  bool reported = false;
  if (paths.empty())
    for (const auto &e : v.value("failure_events", json::array()))
      if (e.at("payload").contains("result")) {
        auto reason = text(e.at("payload").at("result"), "errorMsg");
        if (auto pos = reason.find("Output paths:"); pos != std::string::npos) {
          paths = reason.substr(pos + 13);
          reported = true;
          break;
        }
      }
  out += "<details class=\"output-paths\"><summary>Output paths" +
         std::string(reported ? " · reported" : "") + "</summary><pre>" +
         terminal(hex(paths.empty() ? "No output paths recorded" : paths)) +
         "</pre></details><details class=\"native-result\"><summary>Native "
         "result · " +
         escape(text(*s, "outcome", "incomplete")) + "</summary>";
  bool has_result = false;
  for (auto &e : v.value("failure_events", json::array()))
    if (text(e, "kind") == "nix.build-result") {
      out += "<pre>" + escape(e.at("payload").dump(2)) + "</pre>";
      has_result = true;
    }
  if (!has_result)
    out += "<p class=\"empty\">No native result recorded</p>";
  out += "</details>" + phase_ledger(v, *s) +
         "<section class=\"graph-panel\"><header "
         "class=\"panel-head\"><h2>Dependencies</h2><span>grey: build-platform "
         "tools</span></header><p "
         "id=\"selected-node\" "
         "hidden></p><div id=\"graph-scroll\" class=\"graph-scroll\" "
         "tabindex=\"0\" role=\"region\" aria-label=\"Dependency graph\" "
         "data-static-count=\"" +
         std::to_string(count) + "\">";
  if (count)
    out += "<details data-static id=\"static-inputs-" + escape(id) +
           "\" hx-preserve><summary hx-get=\"./graph?" + escape(query(id)) +
           "\" hx-target=\"#static-rows\" hx-trigger=\"click once\">" +
           std::to_string(count) +
           " static inputs</summary><div id=\"static-rows\"></div></details>";
  for (const auto &r : g.rows)
    if (g.primary.contains(r.drv) && !r.reference)
      out += g.node({r.drv, r.outputs, 1, false, r.dynamic}, true);
  return out + "</div></section></div></section>";
}

std::string web_logs(const json &records, const std::string &run,
                     const std::string &activity, std::uint64_t after,
                     std::uint64_t before) {
  if (before) {
    std::string out;
    for (auto &r : records)
      out += log_row(r);
    return out + earlier(records, log_earlier_rows);
  }
  std::string out;
  auto next = after;
  for (auto &r : records)
    if (number(r, "seq") > after) {
      out += log_row(r);
      next = std::max(next, number(r, "seq"));
    }
  if (!out.empty())
    out = "<div hx-swap-oob=\"beforeend:#log-rows\">" + out + "</div>";
  // A tail response replaces the window, so it carries its own "earlier" state.
  out += earlier(records, after ? 0 : log_tail_rows);
  return out + "<div id=\"log-cursor\" data-after=\"" + std::to_string(next) +
         "\" data-run=\"" + escape(run) + "\" data-activity=\"" +
         escape(activity) + "\"></div>";
}

std::string web_overview(const json &v) {
  auto c = v.value("cohort", json(nullptr));
  auto name = c.is_object() ? text(c, "name") : "Build observatory";
  if (c.is_object()) {
    auto suffix = " · " + std::to_string(c.at("roots").size()) + " roots";
    if (name.ends_with(suffix))
      name.resize(name.size() - suffix.size());
  }
  std::string stopped;
  if (c.is_object()) {
    std::string platform;
    for (const auto &s : v.at("sessions"))
      if (platform.empty())
        platform = parse_name(label(s)).platform;
    stopped = "<p class=\"campaign-meta\">" +
              std::to_string(number(c, "completed")) + " of " +
              std::to_string(c.at("roots").size()) + " roots settled";
    if (!platform.empty())
      stopped += " · " + escape(platform);
    if (auto why = text(c, "stop_reason"); !why.empty()) {
      std::replace(why.begin(), why.end(), '-', ' ');
      stopped += " · admission stopped: " + escape(why);
    }
    stopped += " · <a href=\"./?follow=1\">Follow latest</a></p>";
  }
  return "<section id=\"overview-summary\" data-watch=\"" +
         std::string(watching(v) ? "1" : "0") +
         "\" hx-get=\"./overview\" hx-trigger=\"refresh" +
         (watching(v) ? ", every 2s" : "") +
         "\" hx-swap=\"outerHTML\"><header class=\"summary-head\"><h1>" +
         escape(name) + "</h1><span class=\"record-mode\" data-live=\"" +
         (watching(v) ? "1\">Live" : "0\">Recorded") + "</span></header>" +
         stopped + campaign_line(v) + "</section>";
}

std::string web_page(const json &v, const std::string &run,
                     const std::string &activity, bool follow) {
  bool overview = run.empty() && !follow;
  auto s = overview ? nullptr : session(v, run);
  auto id = s ? text(*s, "run") : run;
  std::string out =
      "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><meta "
      "name=\"viewport\" content=\"width=device-width, "
      "initial-scale=1\"><title>" +
      escape(s ? label(*s) : "Build observatory") +
      " · Filnix</title><script src=\"./htmx.js\" defer></script><script "
      "src=\"./observatory.js\" defer></script><link rel=\"stylesheet\" "
      "href=\"./observatory.css\"></head><body>";
  if (overview)
    return out +
           "<main class=\"overview\"><p class=\"brand\">Filnix <span>/</span> "
           "campaign</p>" +
           web_overview(v) + controls(v) +
           "<div id=\"session-results\" tabindex=\"0\" "
           "role=\"region\" aria-label=\"Campaign roots\">" +
           web_sessions(v, "", "all", "", 0) + "</div></main></body></html>";
  out += "<main class=\"detail-shell\"><nav class=\"detail-nav\"><a "
         "id=\"sessions-back\" "
         "href=\"./\">← All roots</a></nav><div class=\"detail-layout\">" +
         web_state(v, run, activity);
  // A phase or dependency link narrows the console to one derivation's
  // activity; say whose, and offer the way back.
  std::string scope;
  if (!activity.empty())
    for (const auto &a : v.at("activities"))
      if (text(a, "id") == activity) {
        scope = text(a, "drv");
        for (const auto &r : v.at("recipes"))
          if (text(r, "drv") == scope)
            scope = label(r);
      }
  out += "<section class=\"log-panel\"><header class=\"panel-head\"><h2>Build "
         "output</h2><span id=\"log-mode\">" +
         std::string(v.value("live", false) ? "Live" : "Captured") +
         "</span><button id=\"log-follow\">" +
         (v.value("live", false) ? "Pause" : "Follow") +
         "</button><button id=\"log-end\">End</button><label "
         "class=\"log-find\">Find <input id=\"log-find\" type=\"search\" "
         "aria-label=\"Find in loaded output\"></label><label><input "
         "type=\"checkbox\" id=\"log-wrap\" checked>Wrap</label></header>";
  if (!activity.empty())
    out += "<p class=\"log-scope\">Only " +
           escape(scope.empty() ? "one activity" : parse_name(scope).name) +
           " · <a href=\"./?" + escape(query(id)) + "\">Show all output</a></p>";
  out += "<div class=\"log-scroll\" id=\"log-scroll\" role=\"region\" "
         "aria-label=\"Output console\">" +
         earlier(v.at("logs"), log_tail_rows) +
         "<div class=\"log-rows\" id=\"log-rows\" role=\"log\" "
         "aria-label=\"Build output\">";
  for (auto &r : v.at("logs"))
    out += log_row(r);
  if (v.at("logs").empty())
    out += "<p class=\"log-empty\">No captured output</p>";
  return out +
         "</div></div><footer class=\"console-footer\"><span id=\"find-count\">"
         "</span> <span id=\"console-state\" role=\"status\"></span></footer>"
         "<div id=\"log-cursor\" data-after=\"" +
         std::to_string(number(v, "cursor")) + "\" data-run=\"" + escape(id) +
         "\" data-activity=\"" + escape(activity) +
         "\"></div></section></div></main></body></html>";
}
} // namespace campaign

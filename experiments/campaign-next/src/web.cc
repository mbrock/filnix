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
std::string badge(const std::string &s) {
  return "<span class=\"status\" data-status=\"" + escape(s) + "\">" +
         escape(s) + "</span>";
}
std::string lower(std::string s) {
  for (auto &c : s)
    c = std::tolower(static_cast<unsigned char>(c));
  return s;
}
std::string label(const json &s) {
  return text(s, "name", text(s, "drv", "Unknown derivation"));
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
  std::set<std::string> primary, reachable;
  std::vector<Row> rows;
  Graph(const json &v, const json &s)
      : view(v), run(text(s, "run")), root(text(s, "drv")) {
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
    std::string out = "<div class=\"graph-node\" data-name=\"" +
                      escape(name(r.drv)) + "\"" +
                      (reference ? "" : " id=\"" + anchor + "\"") +
                      " style=\"--depth:" + std::to_string(r.depth) + "\">";
    out += "<a href=\"#" + anchor + "\" class=\"node-name\">" +
           (reference ? "reference · " : "") + escape(name(r.drv)) + "</a>";
    if (r.drv == root)
      out += " · root · " + badge(status(view, *session(view, run)));
    auto a = activities.find(r.drv);
    if (a != activities.end()) {
      auto &item = *a->second;
      auto start = item.value("start_elapsed_ns", std::int64_t(0));
      auto end = item.at("stop_elapsed_ns").is_number()
                     ? item.at("stop_elapsed_ns").get<std::int64_t>()
                     : view.value("elapsed_now_ns", std::int64_t(0));
      auto state = text(item, "status");
      if (state == "awaiting-result")
        state = "ended";
      else if (state == "running" && !view.value("live", false))
        state = "last seen running";
      out += "<span class=\"node-activity\">" +
             escape(text(item, "phase", "activity")) + " · " +
             escape(text(item, "machine", "local")) + " · " + escape(state) +
             " · " + seconds(std::max<std::int64_t>(0, end - start)) +
             "</span><a class=\"node-output\" href=\"./?" +
             escape(query(run, text(item, "id"))) + "\">Output</a>";
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

std::string failure(const json &view, const std::string &state) {
  if (state != "failed" && state != "timed-out" && state != "interrupted")
    return {};
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
  std::string phase = "phase unavailable";
  for (const auto &p : view.value("phases", json::array()))
    phase = "last phase · " + text(p, "phase") + " · #" + text(p, "activity");
  return "<div class=\"failure\">" + escape(phase) + " · " + badge(state) +
         " · " + terminal(hex(reason.empty() ? "no recorded reason" : reason)) +
         "</div>";
}

std::string log_row(const json &r) {
  auto activity = text(r, "activity");
  return "<div class=\"log-row\" data-seq=\"" +
         std::to_string(number(r, "seq")) + "\"><time>" +
         seconds(r.value("elapsed_ns", std::int64_t(0))) +
         "</time><button class=\"log-activity\" data-copy=\"" +
         escape(activity) + "\" title=\"Copy activity id\"" +
         (activity.empty() ? " disabled" : "") + ">" +
         (activity.empty() ? "—" : "#" + escape(activity)) + "</button><pre>" +
         terminal(text(r, "bytes_hex")) + "</pre></div>";
}
bool watching(const json &v) {
  return v.value("watch", v.value("live", false));
}
std::string controls(const json &v, const std::string &run, bool overview) {
  std::string out =
      "<form id=\"rail-controls\" hx-get=\"./sessions\" "
      "hx-target=\"#session-results\" hx-trigger=\"change, submit" +
      std::string(watching(v) ? ", every 3s" : "") +
      "\"><input type=\"hidden\" name=\"overview\" value=\"" +
      (overview ? "1" : "0") +
      "\"><input type=\"hidden\" name=\"run\" value=\"" + escape(run) +
      "\"><input type=\"hidden\" id=\"rail-after\" name=\"after\" "
      "value=\"0\"><label>Filter <select name=\"filter\" "
      "id=\"session-filter\">";
  for (auto s :
       {"all", "observing", "built", "already-valid", "incomplete", "failed",
        "interrupted", "timed-out", "successful", "unattempted"})
    out += "<option>" + std::string(s) + "</option>";
  out += "</select></label><label>Find <input name=\"find\" "
         "id=\"session-find\" type=\"search\" "
         "placeholder=\"Name\"></label></form>";
  return out;
}
std::string sidebar(const json &v, const std::string &run) {
  return "<aside class=\"sidebar\"><p class=\"brand\"><a href=\"./\">FILNIX / "
         "CAMPAIGN</a><small>BUILD OBSERVATORY</small></p><h2>SESSIONS</h2>" +
         controls(v, run, false) +
         "<div id=\"session-results\" "
         "tabindex=\"0\" role=\"region\" aria-label=\"Sessions\">" +
         web_sessions(v, run, "all", "", 0) + "</div></aside>";
}
std::string campaign_line(const json &v, bool name = true) {
  if (!v.contains("cohort") || !v.at("cohort").is_object())
    return {};
  const auto &c = v.at("cohort");
  auto roots_label = " · " + std::to_string(c.at("roots").size()) + " roots";
  std::string out =
      "<div class=\"campaign-line\">" +
      (name ? "<b>" + escape(text(c, "name")) + "</b>" : "") +
      (name ? (text(c, "name").ends_with(roots_label) ? "" : roots_label)
            : std::to_string(c.at("roots").size()) + " roots") +
      " · " + std::to_string(number(c, "completed")) + "/" +
      std::to_string(c.at("roots").size()) + " roots settled";
  for (const auto &[key, f, caption] :
       std::vector<std::tuple<std::string, std::string, std::string>>{
           {"succeeded", "successful", "successful"},
           {"failed", "failed", "failed/interrupted"},
           {"timed_out", "timed-out", "timed out"},
           {"unattempted", "unattempted", "unattempted"}})
    out += " · <button data-filter=\"" + f + "\">" +
           std::to_string(number(c, key.c_str())) + " " + caption + "</button>";
  if (!text(c, "stop_reason").empty())
    out += " · admission stopped: " + escape(text(c, "stop_reason"));
  return out + " · <a href=\"./?follow=1\">Follow latest</a></div>";
}
std::string phase_options(const json &v) {
  std::string out = "<option value=\"\">—</option>";
  for (const auto &p : v.value("phases", json::array()))
    out += "<option value=\"" + std::to_string(number(p, "seq")) +
           "\" data-activity=\"" + escape(text(p, "activity")) + "\">" +
           escape(text(p, "phase")) + " · " +
           seconds(p.value("elapsed_ns", std::int64_t(0))) + " · #" +
           escape(text(p, "activity")) + "</option>";
  return out;
}
} // namespace

std::string web_sessions(const json &v, const std::string &run,
                         const std::string &filter, const std::string &find,
                         std::uint64_t after, bool overview) {
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
  if ((filter == "unattempted" ||
       (overview && (filter.empty() || filter == "all"))) &&
      cohort.is_object()) {
    for (std::size_t i = 0; i < cohort.at("roots").size(); ++i)
      if (!attempted.contains(i) &&
          lower(label(cohort.at("roots")[i])).find(lower(find)) !=
              std::string::npos)
        matches.push_back(cohort.at("roots")[i]);
  }
  after = std::min<std::uint64_t>(after, matches.size());
  std::string out =
      "<p class=\"rail-count\" data-after=\"" + std::to_string(after) + "\">" +
      std::to_string(matches.size()) +
      (overview && cohort.is_object() ? " roots</p>" : " sessions</p>");
  auto end = std::min<std::uint64_t>(matches.size(), after + 50);
  if (overview) {
    html::Writer h;
    h.tag("table", {{"class", "campaign-table"}}, [&] {
      h.tag("thead", [&] {
        h.tag("tr", [&] {
          for (auto name : {"Package", "State", "Events", "Output lines"})
            h.tag("th", {{"scope", "col"}}, [&] { h.text(name); });
        });
      });
      h.tag("tbody", [&] {
        for (auto i = after; i < end; ++i) {
          const auto &s = matches[i];
          auto id = text(s, "run"),
               st = id.empty() ? "unattempted" : status(v, s);
          h.tag("tr", [&] {
            h.tag("td", [&] {
              if (id.empty())
                h.text(label(s));
              else {
                auto href = "./?" + query(id) + "&filter=" + url(filter) +
                            "&find=" + url(find);
                h.tag("a", {{"href", href}}, [&] { h.text(label(s)); });
              }
            });
            h.tag("td", [&] {
              h.tag("span", {{"class", "status"}, {"data-status", st}},
                    [&] { h.text(st); });
            });
            for (auto key : {"events", "output_lines"})
              h.tag("td", [&] { h.text(std::to_string(number(s, key))); });
          });
        }
      });
    });
    out += std::move(h).str();
  } else {
    out += "<ul class=\"session-list\">";
    for (auto i = after; i < end; ++i) {
      const auto &s = matches[i];
      auto id = text(s, "run");
      auto tag = id.empty() ? "div" : "a";
      out += "<li><" + std::string(tag) + " class=\"session-link" +
             (id == run ? " selected" : "") + "\"";
      if (!id.empty())
        out += " href=\"./?" + escape(query(id)) +
               "&amp;filter=" + escape(url(filter)) +
               "&amp;find=" + escape(url(find)) + "\"";
      out += "><span class=\"session-title\">" + escape(label(s)) +
             "</span><span class=\"session-sub\">" +
             badge(id.empty() ? "unattempted" : status(v, s)) + " · " +
             std::to_string(number(s, "events")) + " ev</span></" + tag +
             "></li>";
    }
    out += "</ul>";
  }
  if (matches.empty())
    out += "<p class=\"empty\">No sessions · " +
           escape(filter.empty() ? "all" : filter) + "</p>";
  auto page = [&](std::uint64_t offset, const std::string &caption) {
    return "<button hx-get=\"./sessions?" + escape(query(run)) +
           "&amp;filter=" + escape(url(filter)) +
           "&amp;find=" + escape(url(find)) +
           "&amp;after=" + std::to_string(offset) +
           "&amp;overview=" + (overview ? "1" : "0") +
           "\" hx-target=\"#session-results\">" + caption + "</button>";
  };
  out += "<div class=\"paging\">";
  if (after)
    out += page(after >= 50 ? after - 50 : 0, "Previous 50");
  if (end < matches.size())
    out += page(end, "Show next 50");
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
  out += "<div class=\"session-summary\" tabindex=\"0\" role=\"region\" "
         "aria-label=\"Session facts\"><header class=\"summary-head\"><h1>" +
         escape(label(*s)) + "</h1><div>" + badge(st) +
         " <span class=\"record-mode\">" +
         (v.value("live", false) ? "Live · recording" : "Recorded") +
         "</span></div></header>";
  out += campaign_line(v);
  out += "<dl class=\"facts\"><div class=\"drv-fact\"><dt>DERIVATION <button "
         "data-copy=\"" +
         escape(text(*s, "drv")) + "\">Copy drv</button></dt><dd>" +
         escape(text(*s, "drv", "—")) + "</dd></div>";
  for (auto &[caption, value] :
       std::vector<std::pair<std::string, std::string>>{
           {"SYSTEM", text(*s, "system", "—")},
           {"EVENTS", std::to_string(number(*s, "events"))},
           {"OUTPUT LINES", std::to_string(number(*s, "output_lines"))}})
    out += "<div><dt>" + caption + "</dt><dd>" + escape(value) + "</dd></div>";
  out += "</dl><details class=\"native-result\"><summary>Native result · " +
         escape(text(*s, "outcome", "incomplete")) + "</summary>";
  for (auto &e : v.value("failure_events", json::array()))
    if (text(e, "kind") == "nix.build-result")
      out += "<pre>" + escape(e.at("payload").dump(2)) + "</pre>";
  out += "</details><template id=\"phase-options\">" + phase_options(v) +
         "</template></div><section class=\"graph-panel\"><header "
         "class=\"panel-head\"><h2>Dependency graph</h2><span>Static inputs · "
         "activity overlaid</span></header><p id=\"selected-node\" "
         "hidden></p><div id=\"graph-scroll\" class=\"graph-scroll\" "
         "tabindex=\"0\" role=\"region\" aria-label=\"Dependency graph\" "
         "data-static-count=\"" +
         std::to_string(count) + "\">" + failure(v, st);
  out += g.node({g.root, "", 0, false, false}, true);
  auto root_activity = g.activities.find(g.root);
  if (root_activity != g.activities.end()) {
    for (const auto &p : v.value("phases", json::array()))
      if (text(p, "activity") == text(*root_activity->second, "id"))
        out += "<button class=\"phase-row\" data-phase-seq=\"" +
               std::to_string(number(p, "seq")) + "\" data-phase-activity=\"" +
               escape(text(p, "activity")) + "\">" +
               seconds(p.value("elapsed_ns", std::int64_t(0))) + " · " +
               escape(text(p, "phase")) + "</button>";
  }
  if (count)
    out += "<details data-static id=\"static-inputs-" + escape(id) +
           "\" hx-preserve><summary hx-get=\"./graph?" + escape(query(id)) +
           "\" hx-target=\"#static-rows\" hx-trigger=\"click once\">" +
           std::to_string(count) +
           " static inputs</summary><div id=\"static-rows\"></div></details>";
  for (const auto &r : g.rows)
    if (g.primary.contains(r.drv) && !r.reference)
      out += g.node({r.drv, r.outputs, 1, false, r.dynamic}, true);
  return out + "</div></section></section>";
}

std::string web_logs(const json &records, const std::string &run,
                     const std::string &activity, std::uint64_t after) {
  std::string out;
  auto next = after;
  for (auto &r : records)
    if (number(r, "seq") > after) {
      out += log_row(r);
      next = std::max(next, number(r, "seq"));
    }
  if (!out.empty())
    out = "<div hx-swap-oob=\"beforeend:#log-rows\">" + out + "</div>";
  return out + "<div id=\"log-cursor\" data-after=\"" + std::to_string(next) +
         "\" data-run=\"" + escape(run) + "\" data-activity=\"" +
         escape(activity) + "\"></div>";
}

std::string web_overview(const json &v) {
  auto c = v.value("cohort", json(nullptr));
  return "<section id=\"overview-summary\" data-watch=\"" +
         std::string(watching(v) ? "1" : "0") +
         "\" hx-get=\"./overview\" hx-trigger=\"refresh" +
         (watching(v) ? ", every 2s" : "") +
         "\" hx-swap=\"outerHTML\"><header class=\"summary-head\"><h1>" +
         escape(c.is_object() ? text(c, "name") : "Build observatory") +
         "</h1><span class=\"record-mode\">" +
         (watching(v) ? "Live · recording" : "Recorded") + "</span></header>" +
         campaign_line(v, false) + "</section>";
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
           "<main class=\"overview\"><p class=\"brand\">FILNIX / "
           "CAMPAIGN<small>BUILD OBSERVATORY</small></p>" +
           web_overview(v) + controls(v, "", true) +
           "<div id=\"session-results\" tabindex=\"0\" "
           "role=\"region\" aria-label=\"Campaign roots\">" +
           web_sessions(v, "", "all", "", 0, true) +
           "</div></main></body></html>";
  out += "<div class=\"shell\">" + sidebar(v, id) +
         "<main class=\"main\"><div class=\"content\">" +
         web_state(v, run, activity);
  out += "<section class=\"log-panel\"><header class=\"panel-head\"><h2>Build "
         "output</h2><span id=\"log-mode\">" +
         std::string(v.value("live", false) ? "Live" : "Captured") +
         "</span><button id=\"log-follow\">" +
         (v.value("live", false) ? "Pause" : "Follow") +
         "</button><button "
         "id=\"log-end\">End</button><label>Find <input id=\"log-find\" "
         "type=\"search\" aria-label=\"Find in loaded output\"></label><span "
         "id=\"find-count\"></span><label>Phase <select "
         "id=\"log-phase\">" +
         phase_options(v);
  out +=
      "</select></label><a href=\"./?" + escape(query(id)) +
      "\">All output</a><span id=\"console-state\" "
      "role=\"status\"></span></header><div class=\"log-scroll\" "
      "id=\"log-scroll\" tabindex=\"0\" role=\"region\" "
      "aria-label=\"Output console\"><div class=\"log-rows\" id=\"log-rows\" "
      "role=\"log\" aria-label=\"Build output\">";
  for (auto &r : v.at("logs"))
    out += log_row(r);
  if (v.at("logs").empty())
    out += "<p class=\"log-empty\">No captured output</p>";
  return out + "</div></div><div id=\"log-cursor\" data-after=\"" +
         std::to_string(number(v, "cursor")) + "\" data-run=\"" + escape(id) +
         "\" data-activity=\"" + escape(activity) +
         "\"></div></section></div></main></div></body></html>";
}
} // namespace campaign

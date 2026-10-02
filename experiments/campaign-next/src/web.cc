#include "web.hh"

#include <algorithm>
#include <cctype>
#include <iomanip>
#include <map>
#include <set>
#include <sstream>
#include <vector>

namespace campaign {
namespace {

std::string escape(std::string_view value) {
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
    case '\"':
      out += "&quot;";
      break;
    case '\'':
      out += "&#39;";
      break;
    default:
      out += c;
      break;
    }
  }
  return out;
}

std::string string(const json &value, const char *key,
                   std::string fallback = {}) {
  if (!value.is_object() || !value.contains(key) || !value.at(key).is_string())
    return fallback;
  auto result = value.at(key).get<std::string>();
  return result.empty() ? fallback : result;
}

std::uint64_t number(const json &value, const char *key,
                     std::uint64_t fallback = 0) {
  if (!value.is_object() || !value.contains(key) ||
      (!value.at(key).is_number_unsigned() &&
       !value.at(key).is_number_integer()))
    return fallback;
  try {
    auto n = value.at(key).get<std::int64_t>();
    return n < 0 ? fallback : static_cast<std::uint64_t>(n);
  } catch (...) {
    return fallback;
  }
}

std::int64_t signed_number(const json &value, const char *key) {
  if (!value.is_object() || !value.contains(key) ||
      !value.at(key).is_number_integer())
    return 0;
  try {
    return value.at(key).get<std::int64_t>();
  } catch (...) {
    return 0;
  }
}

std::string seconds(std::int64_t ns) {
  std::ostringstream out;
  out << std::fixed << std::setprecision(3) << static_cast<double>(ns) / 1e9;
  return out.str();
}

std::string url_component(std::string_view value) {
  constexpr char digits[] = "0123456789ABCDEF";
  std::string result;
  for (unsigned char c : value) {
    if (std::isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~')
      result += static_cast<char>(c);
    else {
      result += '%';
      result += digits[c >> 4];
      result += digits[c & 15];
    }
  }
  return result;
}

std::string query(const std::string &run, const std::string &activity) {
  std::string result;
  if (!run.empty())
    result += "run=" + url_component(run);
  if (!activity.empty()) {
    if (!result.empty())
      result += '&';
    result += "activity=" + url_component(activity);
  }
  return result;
}

const json *selected_session(const json &view, const std::string &run) {
  if (view.is_object() && view.contains("session") &&
      view.at("session").is_object()) {
    const auto &session = view.at("session");
    if (run.empty() || string(session, "run") == run)
      return &session;
  }
  if (!view.is_object() || !view.contains("sessions") ||
      !view.at("sessions").is_array())
    return nullptr;
  for (const auto &session : view.at("sessions"))
    if (session.is_object() && (run.empty() || string(session, "run") == run))
      return &session;
  return nullptr;
}

std::string status_line(const json &view, const json *session) {
  if (!session)
    return "No recording selected";
  if (view.is_object() && view.contains("live") &&
      view.at("live").is_boolean() && view.at("live").get<bool>())
    return "Live recording · observations are still arriving";
  if (!session->value("complete", false))
    return "Incomplete recording · observer is not known to be active";
  auto outcome = string(*session, "outcome", "incomplete");
  if (outcome == "built")
    return "Built";
  if (outcome == "already-valid")
    return "Already valid";
  if (outcome == "substituted")
    return "Substituted";
  if (outcome == "failed")
    return "Failed";
  if (outcome == "cancelled")
    return "Cancelled";
  if (outcome == "worker-error")
    return "Worker error";
  if (outcome == "recorder-error")
    return "Recorder error";
  if (outcome == "interrupted")
    return "Interrupted";
  return outcome;
}

std::string activity_link(const std::string &run, const std::string &id) {
  return "/?" + query(run, id);
}

std::string anchor_id(const std::string &drv) {
  constexpr char digits[] = "0123456789abcdef";
  std::string id = "drv-";
  for (unsigned char c : drv) {
    id += digits[c >> 4];
    id += digits[c & 15];
  }
  return id;
}

std::string recipe_label(const std::string &drv,
                         const std::map<std::string, const json *> &recipes) {
  auto found = recipes.find(drv);
  if (found != recipes.end()) {
    auto name = string(*found->second, "name");
    if (!name.empty())
      return name;
  }
  return drv.empty() ? "Unknown derivation" : drv;
}

void render_node(std::string &out, const std::string &drv,
                 const std::string &run_id, const std::string &root_drv,
                 const std::string &root_outcome,
                 const std::map<std::string, const json *> &recipes,
                 const std::map<std::string, std::vector<const json *>> &edges,
                 const std::map<std::string, const json *> &activities,
                 std::set<std::string> &visited, std::set<std::string> &stack,
                 std::int64_t elapsed_now, bool live, std::size_t depth,
                 std::size_t &rendered, const std::string &selected_activity,
                 const std::string &outputs = {}) {
  if (++rendered > 500) {
    out +=
        "<li class=\"graph-truncated\">Graph truncated after 500 nodes.</li>";
    return;
  }
  const bool reference = !visited.insert(drv).second;
  const bool cycle = stack.count(drv) != 0;
  const auto id = anchor_id(drv);
  out += "<li class=\"graph-node" + std::string(reference ? " reference" : "") +
         "\"" + (reference ? "" : " id=\"" + id + "\"") +
         "><div class=\"node-line\">";
  out += "<span class=\"tree-mark\" aria-hidden=\"true\">" +
         std::string(reference ? "↳" : "◆") + "</span>";
  auto activity = activities.find(drv);
  const bool has_activity = activity != activities.end();
  auto activity_id =
      has_activity ? string(*activity->second, "id") : std::string{};
  auto href = reference              ? "#" + id
              : !activity_id.empty() ? activity_link(run_id, activity_id)
                                     : "#" + id;
  out += "<a class=\"node-link" +
         std::string(!activity_id.empty() && activity_id == selected_activity
                         ? " selected"
                         : "") +
         "\" href=\"" + escape(href) + "\">" +
         (reference ? "↳ reference · " : "") +
         escape(recipe_label(drv, recipes)) + "</a>";
  if (recipes.find(drv) == recipes.end())
    out +=
        "<span class=\"node-tag unknown\">recipe metadata unavailable</span>";
  if (drv == root_drv && !root_outcome.empty())
    out += "<span class=\"node-tag root-outcome\">root · " +
           escape(root_outcome) + "</span>";
  if (has_activity) {
    const auto &item = *activity->second;
    auto phase = string(item, "phase");
    auto machine = string(item, "machine");
    if (machine.empty())
      machine = "local";
    auto start = signed_number(item, "start_elapsed_ns");
    auto end = start;
    if (item.contains("stop_elapsed_ns") &&
        item.at("stop_elapsed_ns").is_number_integer())
      end = signed_number(item, "stop_elapsed_ns");
    else
      end = elapsed_now;
    auto elapsed = std::max<std::int64_t>(0, end - start);
    auto status = string(item, "status", "observed");
    if (status == "awaiting-result")
      status = "activity ended";
    else if (status == "running" && !live)
      status = "last seen running";
    out += "<span class=\"node-activity\"><b>" +
           escape(phase.empty() ? "activity" : phase) + "</b> · " +
           escape(machine) + " · " + escape(status) + " · " + seconds(elapsed) +
           "s</span>";
  }
  if (!outputs.empty())
    out += "<span class=\"node-tag\">outputs · " + escape(outputs) + "</span>";
  out += "</div>";
  if (reference || cycle || depth >= 40) {
    if (cycle)
      out += "<span class=\"node-tag unknown\">cycle reference</span>";
    else if (depth >= 40)
      out += "<span class=\"node-tag unknown\">depth limit</span>";
    out += "</li>";
    return;
  }
  stack.insert(drv);
  auto found_edges = edges.find(drv);
  if (found_edges != edges.end() && !found_edges->second.empty()) {
    out += "<ul class=\"dependency-children\">";
    for (const auto *edge : found_edges->second) {
      auto child = string(*edge, "child_drv");
      if (edge->value("dynamic", false)) {
        out += "<li class=\"dynamic-edge\"><span class=\"node-tag "
               "unknown\">unknown dynamic dependency</span>";
        if (!child.empty())
          out += " · " + escape(recipe_label(child, recipes));
        out += "</li>";
        continue;
      }
      if (rendered >= 500) {
        out += "<li class=\"graph-truncated\">Remaining dependencies omitted "
               "(500-node rendering limit).</li>";
        break;
      }
      std::string output_names;
      if (edge->contains("outputs") && edge->at("outputs").is_array()) {
        for (const auto &output : edge->at("outputs")) {
          if (!output.is_string())
            continue;
          if (!output_names.empty())
            output_names += ", ";
          output_names += output.get<std::string>();
        }
      }
      render_node(out, child, run_id, root_drv, root_outcome, recipes, edges,
                  activities, visited, stack, elapsed_now, live, depth + 1,
                  rendered, selected_activity, output_names);
    }
    out += "</ul>";
  }
  stack.erase(drv);
  out += "</li>";
}

std::string state_content(const json &view, const std::string &run,
                          const std::string &activity) {
  auto session = selected_session(view, run);
  std::string out =
      "<section class=\"summary-state\" id=\"state\" hx-get=\"/state?" +
      escape(query(run, activity)) +
      "\" hx-trigger=\"every 1s\" hx-swap=\"outerHTML\">";
  out += "<div class=\"summary-head\"><div><p class=\"eyebrow\">SESSION "
         "OBSERVATION · DEPENDENCY GRAPH</p>";
  out += "<h1>" +
         escape(session ? string(*session, "name",
                                 string(*session, "drv", "Build session"))
                        : "Build activity") +
         "</h1></div>";
  out += "<p class=\"state-pill\" role=\"status\">" +
         escape(status_line(view, session)) + "</p></div>";
  if (!session) {
    out += "<div class=\"empty\"><h2>No build session to show</h2><p>When a "
           "recording is available, its activity and captured output will "
           "appear here.</p></div></section>";
    return out;
  }
  auto run_id = string(*session, "run", run);
  const auto root_drv = string(*session, "drv");
  auto drv = root_drv;
  out += "<dl class=\"facts\"><div><dt>Derivation</dt><dd title=\"" +
         escape(drv) + "\">" + escape(drv.empty() ? "—" : drv) + "</dd></div>";
  out += "<div><dt>System</dt><dd>" + escape(string(*session, "system", "—")) +
         "</dd></div>";
  out += "<div><dt>Events</dt><dd>" +
         std::to_string(number(*session, "events")) + "</dd></div>";
  out += "<div><dt>Output lines</dt><dd>" +
         std::to_string(number(*session, "output_lines")) + "</dd></div></dl>";
  auto root_outcome = session->value("complete", false)
                          ? string(*session, "outcome")
                          : std::string{};
  out += "<div class=\"graph-heading\"><div><h2>Dependency "
         "graph</h2><p>Recorded static inputs · activity observations "
         "overlaid</p></div><a href=\"/?run=" +
         escape(url_component(run_id)) + "\">Show all output</a></div>";
  std::map<std::string, const json *> recipes;
  std::map<std::string, std::vector<const json *>> edges;
  std::map<std::string, const json *> activities_by_drv;
  if (view.contains("recipes") && view.at("recipes").is_array())
    for (const auto &item : view.at("recipes"))
      if (item.is_object())
        recipes[string(item, "drv")] = &item;
  if (view.contains("edges") && view.at("edges").is_array())
    for (const auto &item : view.at("edges"))
      if (item.is_object())
        edges[string(item, "parent_drv")].push_back(&item);
  if (view.contains("activities") && view.at("activities").is_array())
    for (const auto &item : view.at("activities"))
      if (item.is_object() && !string(item, "drv").empty())
        activities_by_drv[string(item, "drv")] = &item;
  for (auto &[parent, children] : edges) {
    (void)parent;
    std::sort(children.begin(), children.end(),
              [&](const json *a, const json *b) {
                auto left = string(*a, "child_drv");
                auto right = string(*b, "child_drv");
                auto left_label = recipe_label(left, recipes);
                auto right_label = recipe_label(right, recipes);
                return left_label == right_label ? left < right
                                                 : left_label < right_label;
              });
  }
  if (drv.empty())
    out += "<p class=\"empty-inline\">This session has no root derivation to "
           "graph.</p>";
  else {
    out += "<ul class=\"dependency-graph\">";
    std::set<std::string> visited, stack;
    std::size_t rendered = 0;
    render_node(out, drv, run_id, root_drv, root_outcome, recipes, edges,
                activities_by_drv, visited, stack,
                signed_number(view, "elapsed_now_ns"),
                view.value("live", false), 0, rendered, activity);
    out += "</ul>";
  }
  return out + "</section>";
}

std::string log_row(const json &record) {
  auto seq = number(record, "seq");
  std::string bytes;
  try {
    bytes = unhex(string(record, "bytes_hex"));
  } catch (...) {
    bytes = "[invalid encoded output]";
  }
  // Replace malformed UTF-8 with U+FFFD before HTML escaping. ASCII control
  // bytes other than whitespace are shown as replacement characters.
  std::string safe;
  for (std::size_t i = 0; i < bytes.size();) {
    auto c = static_cast<unsigned char>(bytes[i]);
    if (c < 0x80) {
      if (c == '\n' || c == '\r' || c == '\t' || c >= 0x20)
        safe += static_cast<char>(c);
      else
        safe += "\xef\xbf\xbd";
      ++i;
      continue;
    }
    std::size_t length = c >= 0xF0 && c <= 0xF4   ? 4
                         : c >= 0xE0 && c <= 0xEF ? 3
                         : c >= 0xC2 && c <= 0xDF ? 2
                                                  : 0;
    bool valid = length && i + length <= bytes.size();
    for (std::size_t j = 1; valid && j < length; ++j)
      valid = (static_cast<unsigned char>(bytes[i + j]) & 0xC0) == 0x80;
    if (valid && length == 3) {
      auto b = static_cast<unsigned char>(bytes[i + 1]);
      valid = !(c == 0xE0 && b < 0xA0) && !(c == 0xED && b >= 0xA0);
    }
    if (valid && length == 4) {
      auto b = static_cast<unsigned char>(bytes[i + 1]);
      valid = !(c == 0xF0 && b < 0x90) && !(c == 0xF4 && b >= 0x90);
    }
    if (valid) {
      safe.append(bytes, i, length);
      i += length;
    } else {
      safe += "\xef\xbf\xbd";
      ++i;
    }
  }
  std::string out = "<div class=\"log-row\"";
  out += " data-seq=\"" + std::to_string(seq) + "\"><time>" +
         escape(seconds(signed_number(record, "elapsed_ns"))) +
         "s</time><span class=\"log-activity\" title=\"" +
         escape(string(record, "activity")) + "\">";
  auto activity = string(record, "activity");
  if (!activity.empty())
    out += "#" + escape(activity);
  else
    out += "—";
  out += "</span><pre>" + escape(safe) + "</pre></div>";
  return out;
}

std::string cursor(std::uint64_t seq, const std::string &run,
                   const std::string &activity) {
  std::string href = "/logs?" + query(run, activity);
  href += (href.find('?') == std::string::npos ? "?" : "&");
  href += "after=" + std::to_string(seq);
  return "<div class=\"log-cursor\" id=\"log-cursor\" hx-get=\"" +
         escape(href) +
         "\" hx-trigger=\"every 1s\" hx-swap=\"outerHTML\" "
         "aria-hidden=\"true\"></div>";
}

std::string sidebar(const json &view, const std::string &selected_run,
                    bool oob) {
  std::string out = "<aside class=\"sidebar\" id=\"sidebar\"";
  if (oob)
    out += " hx-swap-oob=\"outerHTML\"";
  out += "><p class=\"brand\">FILNIX / CAMPAIGN<small>BUILD "
         "OBSERVATORY</small></p><h2 class=\"side-label\">SESSIONS</h2>";
  const auto &sessions = view.at("sessions");
  if (sessions.empty())
    out += "<p class=\"empty-inline\">No recorded sessions yet.</p>";
  else {
    out += "<ul class=\"session-list\">";
    for (const auto &item : sessions) {
      auto id = string(item, "run");
      auto title = string(item, "name", string(item, "drv", "Build session"));
      auto outcome = string(item, "outcome", "incomplete");
      if (id == selected_run && view.value("live", false))
        outcome = "observing";
      out += "<li><a class=\"session-link" +
             std::string(id == selected_run ? " selected" : "") +
             "\" href=\"/?run=" + escape(url_component(id)) +
             "\"><span class=\"session-title\">" + escape(title) +
             "</span><span class=\"session-sub\"><span>" + escape(outcome) +
             "</span><span>" + std::to_string(number(item, "events")) +
             " ev</span></span></a></li>";
    }
    out += "</ul>";
  }
  return out + "</aside>";
}

} // namespace

std::string web_state(const json &view, const std::string &run,
                      const std::string &activity) {
  auto session = selected_session(view, run);
  return state_content(view, run, activity) +
         sidebar(view, session ? string(*session, "run", run) : run, true);
}

std::string web_logs(const json &records, const std::string &run,
                     const std::string &activity, std::uint64_t after) {
  std::string out;
  auto next = after;
  if (records.is_array()) {
    for (const auto &record : records) {
      if (!record.is_object())
        continue;
      auto seq = number(record, "seq");
      if (seq <= after)
        continue;
      out += log_row(record);
      next = std::max(next, seq);
    }
  }
  // beforeend inserts the wrapper's children, not the wrapper itself.
  if (!out.empty())
    out = "<div hx-swap-oob=\"beforeend:#log-rows\">" + out + "</div>";
  return out + cursor(next, run, activity);
}

std::string web_page(const json &view, const std::string &run,
                     const std::string &activity) {
  auto session = selected_session(view, run);
  auto selected_run = session ? string(*session, "run", run) : run;
  std::string out =
      "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><meta "
      "name=\"viewport\" content=\"width=device-width, "
      "initial-scale=1\"><title>Build observatory</title><script "
      "src=\"/htmx.js\" defer></script><style>";
  out += R"CSS(
:root{color-scheme:light;--paper:#f5f5ef;--panel:#fffefa;--ink:#26332e;--muted:#758078;--line:#dce1d9;--green:#315b46;--green-soft:#e8efe9;--amber:#ad7529;--slate:#596a72;font:14px/1.45 ui-sans-serif,system-ui,-apple-system,"Segoe UI",sans-serif}*{box-sizing:border-box}body{margin:0;background:var(--paper);color:var(--ink)}a{color:var(--green);text-decoration:none}a:hover{text-decoration:underline}a:focus-visible{outline:3px solid #d69a43;outline-offset:3px}.shell{min-height:100vh;display:grid;grid-template-columns:250px minmax(0,1fr)}.sidebar{background:#eeefe8;border-right:1px solid var(--line);padding:25px 16px;min-width:0}.brand{font:700 16px/1.2 ui-monospace,SFMono-Regular,monospace;letter-spacing:-.04em;color:var(--green);margin:0 8px 28px}.brand small{display:block;color:var(--muted);font:500 10px/1.4 ui-monospace,monospace;letter-spacing:.12em;margin-top:6px}.side-label,.eyebrow{font:700 10px/1.3 ui-monospace,SFMono-Regular,monospace;letter-spacing:.12em;color:var(--muted)}.side-label{margin:0 8px 10px}.session-list{list-style:none;margin:0;padding:0;display:grid;gap:4px}.session-link{display:block;padding:10px 9px;border-radius:5px;color:var(--ink);min-width:0}.session-link:hover,.session-link.selected{background:var(--green-soft);text-decoration:none}.session-title{display:block;font-weight:650;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.session-sub{display:flex;justify-content:space-between;gap:8px;color:var(--muted);font:11px/1.5 ui-monospace,monospace;margin-top:3px}.main{min-width:0;padding:32px clamp(16px,4vw,54px) 44px}.content{max-width:1120px;margin:0 auto}.summary-state{min-width:0}.summary-head{display:flex;justify-content:space-between;align-items:flex-start;gap:20px;padding-bottom:20px;border-bottom:1px solid var(--line)}.eyebrow{margin:0 0 7px}h1{font-size:clamp(21px,3vw,30px);line-height:1.2;letter-spacing:-.035em;margin:0;overflow-wrap:anywhere}.state-pill{margin:1px 0 0;padding:6px 10px;border:1px solid #d3dbd4;border-radius:3px;color:var(--green);background:#edf2ed;font-size:12px;max-width:52%;text-align:right}.facts{display:grid;grid-template-columns:2fr 1fr 1fr 1fr;gap:12px;margin:19px 0 26px}.facts div{min-width:0}.facts dt{font:700 10px ui-monospace,monospace;letter-spacing:.08em;text-transform:uppercase;color:var(--muted)}.facts dd{margin:5px 0 0;font:12px/1.45 ui-monospace,monospace;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.activity-head{display:flex;align-items:baseline;justify-content:space-between;gap:12px;padding-bottom:9px;border-bottom:1px solid var(--line)}h2{font-size:14px;margin:0;font-weight:700}.activity-head a{font-size:12px}.activities{list-style:none;margin:0;padding:0}.activities li{border-bottom:1px solid var(--line)}.activity-row{display:grid;grid-template-columns:52px minmax(0,1fr) auto;align-items:center;gap:11px;padding:11px 8px;color:var(--ink);min-width:0}.activity-row:hover,.activity-row.selected{background:var(--green-soft);text-decoration:none}.activity-id,.activity-meta,.activity-copy small{font:11px/1.4 ui-monospace,monospace;color:var(--muted)}.activity-copy{min-width:0}.activity-copy strong{display:block;font-size:12px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-weight:600}.activity-copy small{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin-top:2px}.activity-meta{text-align:right;display:grid;gap:2px}.activity-status{color:var(--amber)}.empty,.empty-inline{color:var(--muted)}.empty{margin-top:28px;padding:25px;background:var(--panel);border:1px solid var(--line)}.empty h2{margin-bottom:6px}.empty p{margin:0}.empty-inline{padding:14px 8px}.log-panel{margin-top:30px;background:var(--panel);border:1px solid var(--line);min-width:0}.log-head{display:flex;justify-content:space-between;align-items:baseline;gap:12px;padding:12px 14px;border-bottom:1px solid var(--line)}.log-head p{font:11px ui-monospace,monospace;color:var(--muted);margin:0}.log-rows{max-height:52vh;min-height:150px;overflow:auto;overscroll-behavior:contain}.log-row{display:grid;grid-template-columns:62px 48px minmax(0,1fr);gap:9px;padding:6px 12px;border-bottom:1px solid #edf0ea;align-items:start}.log-row time,.log-activity{font:10px/1.6 ui-monospace,monospace;color:var(--muted);white-space:nowrap}.log-activity{color:var(--slate)}.log-row pre{font:12px/1.5 ui-monospace,SFMono-Regular,monospace;margin:0;white-space:pre;overflow-wrap:normal;min-width:0}.log-rows{overflow-x:auto}.log-empty{padding:18px;color:var(--muted);font-size:12px}.log-cursor{height:1px}@media(max-width:700px){.shell{grid-template-columns:minmax(0,1fr)}.sidebar{padding:15px 16px;border-right:0;border-bottom:1px solid var(--line)}.brand{margin:0 0 13px}.session-list{display:flex;overflow-x:auto;padding-bottom:3px}.session-list li{flex:0 0 min(230px,70vw)}.session-link{padding:8px}.main{padding:22px 14px 32px}.facts{grid-template-columns:minmax(0,2fr) minmax(0,1fr);gap:14px}.summary-head{display:block}.state-pill{display:inline-block;text-align:left;max-width:100%;margin-top:12px}.activity-row{grid-template-columns:38px minmax(0,1fr) auto;gap:7px;padding:10px 4px}.activity-meta{font-size:10px}.log-panel{margin-left:-5px;margin-right:-5px}.log-row{grid-template-columns:55px 38px minmax(0,1fr);gap:6px;padding:6px 8px}.log-rows{max-height:45vh}}@media(max-width:390px){.activity-row{grid-template-columns:34px minmax(0,1fr) auto;gap:5px}.activity-status{max-width:78px;overflow:hidden;text-overflow:ellipsis}.facts{grid-template-columns:1fr 1fr}.log-head{padding:10px}.log-row{grid-template-columns:48px 34px minmax(0,1fr);gap:5px}}
)CSS";
  out += R"CSS(
.graph-heading{display:flex;align-items:end;justify-content:space-between;gap:14px;margin:4px 0 10px;padding-bottom:9px;border-bottom:1px solid var(--line)}.graph-heading p{margin:3px 0 0;color:var(--muted);font-size:11px}.graph-heading>a{font-size:12px;white-space:nowrap}.dependency-graph,.dependency-children{list-style:none;margin:0;padding:0}.dependency-graph{padding:8px 0 4px;border-left:1px solid #cbd5cc}.dependency-children{margin:2px 0 3px 13px;padding-left:16px;border-left:1px solid #d7ded7}.graph-node{position:relative;padding:1px 0}.node-line{display:flex;align-items:baseline;gap:8px;min-height:27px;flex-wrap:wrap}.tree-mark{width:15px;margin-left:-8px;background:var(--paper);color:#77917e;text-align:center;font-size:10px}.node-link{font:600 12px/1.45 ui-monospace,SFMono-Regular,monospace;overflow-wrap:anywhere}.node-link.selected{background:var(--green-soft);outline:2px solid var(--green-soft)}.reference .node-link{color:#67756c}.node-tag{display:inline-block;padding:1px 6px;border-radius:3px;background:#edf0eb;color:#68756c;font:10px/1.5 ui-monospace,monospace}.node-tag.unknown,.dynamic-edge{color:#98691f}.node-tag.unknown{background:#f5efdf}.node-tag.root-outcome{background:#e5eee7;color:var(--green)}.node-activity{color:var(--muted);font:10px/1.5 ui-monospace,monospace;overflow-wrap:anywhere}.node-activity b{font-weight:600;color:var(--slate)}.dynamic-edge,.graph-truncated{padding:3px 6px;font:10px/1.5 ui-monospace,monospace}.graph-truncated{color:#8e6726}
)CSS";
  out += ".log-activity{min-width:0;overflow:hidden;text-overflow:ellipsis}"
         "</style></head><body><div class=\"shell\">" +
         sidebar(view, selected_run, false);
  out +=
      "<main class=\"main\"><div class=\"content\">" +
      state_content(view, run, activity) +
      "<section class=\"log-panel\" aria-labelledby=\"logs-title\"><header "
      "class=\"log-head\"><h2 id=\"logs-title\">Build output</h2><p>Captured "
      "output · observer timeline</p></header><div class=\"log-rows\" "
      "id=\"log-rows\" role=\"log\" aria-label=\"Captured build output\">";
  const auto &logs =
      view.is_object() && view.contains("logs") && view.at("logs").is_array()
          ? view.at("logs")
          : json::array();
  if (logs.empty())
    out += "<p class=\"log-empty\">No output observations yet. Activity stop "
           "alone does not establish a successful build.</p>";
  else {
    std::size_t shown = 0;
    for (const auto &record : logs) {
      if (shown++ >= 2000)
        break;
      out += log_row(record);
    }
  }
  out += "</div>";
  auto after = number(view, "cursor");
  if (!logs.empty())
    after = std::max(after, number(logs.back(), "seq"));
  out += cursor(after, selected_run, activity);
  out += R"HTML(</section></div></main></div><script>
document.addEventListener('DOMContentLoaded', function () {
  const box = document.getElementById('log-rows');
  let follow = true;
  box.scrollTop = box.scrollHeight;
  box.addEventListener('scroll', function () {
    follow = box.scrollHeight - box.scrollTop - box.clientHeight < 40;
  });
  new MutationObserver(function () {
    const empty = box.querySelector('.log-empty');
    if (empty && box.querySelector('.log-row')) empty.remove();
    while (box.children.length > 2000) box.firstElementChild.remove();
    if (follow) box.scrollTop = box.scrollHeight;
  }).observe(box, {childList: true});
});
</script></body></html>)HTML";
  return out;
}

} // namespace campaign

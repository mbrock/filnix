#include "analysis.hh"

#include <regex>

namespace campaign {
namespace {

std::string strip_sgr(std::string line) {
  static const std::regex sgr("\x1b\\[[0-9;]*m");
  line = std::regex_replace(line, sgr, "");
  while (!line.empty() && (line.back() == '\r' || line.back() == '\n'))
    line.pop_back();
  return line;
}

std::string trim(std::string s) {
  auto a = s.find_first_not_of(" \t");
  auto b = s.find_last_not_of(" \t");
  return a == std::string::npos ? "" : s.substr(a, b - a + 1);
}

// At most `limit` bytes, without splitting a UTF-8 sequence.
std::string clip(std::string s, std::size_t limit) {
  if (s.size() <= limit)
    return s;
  s.resize(limit);
  while (!s.empty() && (static_cast<unsigned char>(s.back()) & 0xc0) == 0x80)
    s.pop_back();
  if (!s.empty() && static_cast<unsigned char>(s.back()) >= 0xc0)
    s.pop_back();
  return s;
}

// Builder bytes need not be UTF-8; JSON text must be.
std::string utf8(const std::string &s) {
  return json::parse(json(s).dump(-1, ' ', false,
                                  json::error_handler_t::replace))
      .get<std::string>();
}

bool success(const std::string &outcome) {
  return outcome == "built" || outcome == "already-valid" ||
         outcome == "substituted" || outcome == "resolves-to-already-valid";
}

} // namespace

std::string first_error(const std::vector<std::string> &lines,
                        const std::string &phase) {
  // The nanofil survey's order of preference (nanofil/survey/run.py): its
  // own message, the wrapper's refusal, configure's verdict, a compiler or
  // make error, ...; a nanofil error from a probe's config.log only when
  // nothing else says why. Searched from the start of the last phase.
  static const std::vector<std::pair<std::regex, bool>> patterns = [] {
    std::vector<std::pair<std::regex, bool>> p;
    for (auto [pattern, anywhere] :
         {std::pair{"^nanofil: ", true}, {"^nanofil-survey-cc: ", true},
          {"configure: error: ", false}, {"\\berror: ", false},
          {"Error [0-9]+", false}, {"\\bFAIL\\b", false},
          {"^nanofil-survey-config: ", true}, {"No such file", false}})
      p.emplace_back(std::regex(pattern), anywhere);
    return p;
  }();
  std::size_t start = 0;
  for (std::size_t i = 0; i < lines.size(); ++i)
    if (lines[i] == "Running phase: " + phase)
      start = i;
  for (const auto &[pattern, anywhere] : patterns) {
    for (std::size_t i = start; i < lines.size(); ++i)
      if (std::regex_search(lines[i], pattern))
        return clip(trim(lines[i]), 300);
    if (anywhere)
      for (std::size_t i = 0; i < start; ++i)
        if (std::regex_search(lines[i], pattern))
          return clip(trim(lines[i]), 300);
  }
  for (auto i = lines.size(); i-- > 0;)
    if (!trim(lines[i]).empty())
      return clip(trim(lines[i]), 300);
  return "";
}

json analyze(const json &facts) {
  const auto &summary = facts.at("summary");
  auto outcome = summary.value("outcome", "incomplete");
  json a = {
      {"outcome", outcome},
      {"native_status", facts.value("native_status", json(nullptr))},
      {"wall_ns", facts.value("duration_ns", json(nullptr))},
      {"build_ns", nullptr},
      {"machine", ""},
      {"failed_drv", facts.value("failed_drv", "")},
      {"phase", ""},
      {"error", ""},
      {"cause", ""},
      {"counts", nullptr},
      {"outputs", success(outcome) ? summary.value("outputs", json::array())
                                   : json::array()},
  };
  if (facts.at("cause_hex").is_string())
    a["cause"] = utf8(clip(
        trim(strip_sgr(unhex(facts.at("cause_hex").get<std::string>()))), 2000));
  const auto &root = facts.at("root_build");
  if (root.is_object()) {
    a["machine"] = root.value("machine", "");
    if (root.at("stop_elapsed_ns").is_number() &&
        root.at("start_elapsed_ns").is_number())
      a["build_ns"] = root.at("stop_elapsed_ns").get<std::int64_t>() -
                      root.at("start_elapsed_ns").get<std::int64_t>();
  }
  const auto &failed = facts.value("failed_build", json(nullptr));
  const auto &build = failed.is_object() ? failed : root;
  if (failed.is_object() && root.is_null())
    a["machine"] = failed.value("machine", "");
  std::vector<std::string> lines;
  for (const auto &hex_line : facts.at("log_hex")) {
    auto text = unhex(hex_line.get<std::string>());
    // A record normally holds one line; split defensively.
    std::size_t from = 0;
    while (from <= text.size()) {
      auto end = text.find('\n', from);
      lines.push_back(strip_sgr(text.substr(
          from, end == std::string::npos ? std::string::npos : end - from)));
      if (end == std::string::npos)
        break;
      from = end + 1;
      if (from == text.size())
        break;
    }
  }
  std::string phase;
  if (build.is_object() && build.value("phase_hex", "") != "")
    phase = unhex(build.at("phase_hex").get<std::string>());
  if (phase.empty())
    for (const auto &line : lines)
      if (line.starts_with("Running phase: "))
        phase = line.substr(15);
  a["phase"] = utf8(phase);
  if (!success(outcome) && outcome != "cancelled" && outcome != "incomplete")
    a["error"] = utf8(first_error(lines, phase));
  static const std::regex counts(
      "nanofil-survey: ([0-9]+) objects, ([0-9]+) C\\+\\+, ([0-9]+) fallbacks");
  for (auto i = lines.size(); i-- > 0;) {
    std::smatch m;
    if (std::regex_search(lines[i], m, counts)) {
      a["counts"] = {{"objects", std::stoll(m[1])},
                     {"cxx", std::stoll(m[2])},
                     {"fallbacks", std::stoll(m[3])}};
      break;
    }
  }
  return a;
}

} // namespace campaign

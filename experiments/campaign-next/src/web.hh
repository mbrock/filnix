#pragma once

#include "journal.hh"

#include <cstdint>
#include <string>

namespace campaign {

std::string web_page(const json &view, const std::string &run,
                     const std::string &activity, bool follow = false);
std::string web_overview(const json &view);
std::string web_state(const json &view, const std::string &run,
                      const std::string &activity);
std::string web_logs(const json &records, const std::string &run,
                     const std::string &activity, std::uint64_t after);
std::string web_sessions(const json &view, const std::string &run,
                         const std::string &filter, const std::string &find,
                         std::uint64_t after);
std::string web_graph(const json &view, const std::string &run,
                      std::uint64_t after, const std::string &node);

} // namespace campaign

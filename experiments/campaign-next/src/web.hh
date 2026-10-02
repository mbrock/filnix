#pragma once

#include "journal.hh"

#include <cstdint>
#include <string>

namespace campaign {

std::string web_page(const json &view, const std::string &run,
                     const std::string &activity);
std::string web_state(const json &view, const std::string &run,
                      const std::string &activity);
std::string web_logs(const json &records, const std::string &run,
                     const std::string &activity, std::uint64_t after);

} // namespace campaign

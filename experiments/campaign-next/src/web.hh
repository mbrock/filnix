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
                     const std::string &activity, std::uint64_t after,
                     std::uint64_t before = 0);
std::string web_sessions(const json &view, const std::string &run,
                         const std::string &filter, const std::string &find,
                         std::uint64_t after);
std::string web_graph(const json &view, const std::string &run,
                      std::uint64_t after, const std::string &node);

// The service's campaign list (Catalog::campaigns) at the site root.
std::string web_campaigns(const json &campaigns);
// A survey campaign's packages, filcc (`ref`) and nanofil (`nf`) side by
// side, from {campaign, roots} with each root's latest attempt.
std::string web_survey(const json &results);
// The survey's words for one root's latest attempt (nanofil/survey/run.py).
std::string survey_status(const json &root);

} // namespace campaign

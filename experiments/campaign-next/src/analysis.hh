#pragma once

#include "journal.hh"

#include <vector>

namespace campaign {

// One attempt's result from Dataset::attempt_facts: outcome, native status,
// times, machine, failing derivation and phase, the first error line by the
// nanofil survey's rules, and its "nanofil-survey:" counts. Pure; touches
// no database, so it may run on any thread.
json analyze(const json &facts);
std::string first_error(const std::vector<std::string> &lines,
                        const std::string &phase);

} // namespace campaign

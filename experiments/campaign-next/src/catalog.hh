#pragma once

#include "journal.hh"
#include <duckdb.hpp>

namespace campaign {

// The service's small catalog: campaigns, their roots and every attempt.
// Like Dataset, all of it belongs to one blocking-pool worker thread.
class Catalog {
public:
  explicit Catalog(const std::string &path);

  // Every campaign with its root and latest-attempt counts.
  json campaigns(bool all = false);
  json campaign(const std::string &id);
  // Each root with its latest attempt, in manifest order.
  json roots(const std::string &id);
  json attempts(const std::string &id);
  // Campaigns and roots the scheduler restores after a restart.
  json restore();
  std::string campaign_of_run(const std::string &run);
  std::string find_fingerprint(const std::string &fingerprint);
  json publication_outputs();

  void insert_campaign(const json &campaign, const json &roots);
  // Updates the named columns of one campaign row.
  void update_campaign(const std::string &id, const json &fields);
  void set_root_state(const std::string &id, const std::string &name,
                      const std::string &state);
  void insert_attempt(const json &attempt);
  void finish_attempt(const std::string &id, const std::string &name,
                      int attempt, const json &result);

private:
  duckdb::DBConfig config_;
  duckdb::DuckDB database_;
  duckdb::Connection connection_;
  void exec(const std::string &query);
  json rows(const std::string &query);
};

} // namespace campaign

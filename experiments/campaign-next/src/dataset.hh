#pragma once

#include "journal.hh"
#include <duckdb.hpp>
#include <map>

namespace campaign {

// Every method, including construction/destruction, belongs to the one
// persistent blocking-pool worker. Only owned JSON crosses back to the deck.
class Dataset {
public:
  // `read_only` opens without writing anything, not even WAL recovery,
  // so archives on a read-only mount can be read.
  Dataset(const std::string &path, bool writable,
          const std::string &memory_limit = "1 GiB", bool read_only = false);
  void append(const json &batch);
  json summary(std::string run = "");
  json events(std::string run, std::uint64_t after);
  json publication_outputs();
  json resources();
  // A non-null `cohort` (a service campaign: id, name, roots) scopes the
  // view; otherwise the selected run's recorded cohort, if any, does.
  json view(std::string run, std::string activity, bool detail = true,
            json cohort = nullptr);
  // The facts one attempt's analysis needs: its summary and timings, the
  // root's own build, the failing derivation and the relevant log lines.
  json attempt_facts(const std::string &run);
  // The runs a recording holds, with their request and summary.
  json run_list();
  // Identifies a recording's content: watermark, run count, first/last run.
  std::string fingerprint();
  // Forward from `after`; or the latest `tail_rows`; or the rows before
  // `before`, newest last. Windows are bounded; callers page explicitly.
  json logs(std::string run, std::string activity, std::uint64_t after,
            bool tail = false, std::uint64_t before = 0);
  json export_to(const std::string &directory);

private:
  duckdb::DBConfig config_;
  duckdb::DuckDB database_;
  duckdb::Connection connection_;
  std::map<std::string, Projection> projections_;
  std::uint64_t watermark_ = 0;
  unsigned schema_version_ = 2;
  void exec(const std::string &query);
  json rows(const std::string &query);
  std::string select_run(std::string run);
};

} // namespace campaign

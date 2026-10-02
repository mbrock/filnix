#pragma once

#include "journal.hh"
#include <duckdb.hpp>
#include <map>

namespace campaign {

// Every method, including construction/destruction, belongs to the one
// persistent blocking-pool worker. Only owned JSON crosses back to the deck.
class Dataset {
public:
  Dataset(const std::string &path, bool writable);
  void append(const json &batch);
  json summary(std::string run = "");
  json events(std::string run, std::uint64_t after);
  json view(std::string run, std::string activity);
  json logs(std::string run, std::string activity, std::uint64_t after,
            bool tail = false);
  json export_to(const std::string &directory);

private:
  duckdb::DuckDB database_;
  duckdb::Connection connection_;
  std::map<std::string, Projection> projections_;
  std::uint64_t watermark_ = 0;
  void exec(const std::string &sql);
  json rows(const std::string &sql);
  std::string select_run(std::string run);
};

} // namespace campaign

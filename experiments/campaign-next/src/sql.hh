#pragma once

#include "journal.hh"
#include <duckdb.hpp>

namespace campaign::sql {

inline std::string quote(std::string_view value) {
  std::string result = "'";
  for (char c : value) {
    if (!c)
      throw std::runtime_error("NUL in SQL text value");
    result += c;
    if (c == '\'')
      result += c;
  }
  return result + "'";
}

inline void exec(duckdb::Connection &connection, const std::string &query) {
  auto result = connection.Query(query);
  if (result->HasError())
    throw std::runtime_error(result->GetError());
}

inline json rows(duckdb::Connection &connection, const std::string &query) {
  auto result = connection.Query("SELECT to_json(q) FROM (" + query + ") q");
  if (result->HasError())
    throw std::runtime_error(result->GetError());
  auto output = json::array();
  for (duckdb::idx_t i = 0; i < result->RowCount(); ++i)
    output.push_back(json::parse(result->GetValue(0, i).ToString()));
  return output;
}

} // namespace campaign::sql

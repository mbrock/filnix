#include "dataset.hh"

#include <filesystem>
#include <fstream>

namespace campaign {
namespace {

std::string quote(std::string_view value) {
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

std::string blob(const std::string &hex_bytes) {
  // Validate before placing encoded arbitrary bytes in SQL. BLOBs, not
  // DuckDB VARCHARs, are the authority for logger strings and output.
  unhex(hex_bytes);
  return "from_hex(" + quote(hex_bytes) + ")";
}

std::string id(const json &payload, const char *key) {
  return std::to_string(payload.at(key).get<std::uint64_t>());
}

std::string open_path(const std::string &path, bool writable) {
  if (!writable && !std::filesystem::is_regular_file(path))
    throw std::runtime_error("database does not exist: " + path);
  return path;
}

} // namespace

Dataset::Dataset(const std::string &path, bool writable)
    : database_(open_path(path, writable)), connection_(database_) {
  // The application owns this database in one process. Offline commands
  // never append; opening normally also permits DuckDB's WAL recovery.
  auto tables = rows("SELECT table_name FROM information_schema.tables "
                     "WHERE table_schema='main'");
  if (tables.empty() && writable) {
    exec(R"SQL(
BEGIN;
CREATE TABLE campaign_meta(schema_version INTEGER);
INSERT INTO campaign_meta VALUES (1);
CREATE TABLE events("offset" UBIGINT PRIMARY KEY, run VARCHAR, seq UBIGINT,
    wall_ns BIGINT, elapsed_ns BIGINT, kind VARCHAR, payload JSON,
    UNIQUE(run, seq));
CREATE TABLE runs(run VARCHAR PRIMARY KEY, drv VARCHAR, store VARCHAR,
    name VARCHAR, system VARCHAR, start_wall_ns BIGINT, last_offset UBIGINT,
    summary JSON);
CREATE TABLE recipes(run VARCHAR, drv VARCHAR, name VARCHAR, system VARCHAR,
    PRIMARY KEY(run, drv));
CREATE TABLE edges(run VARCHAR, parent_drv VARCHAR, child_drv VARCHAR,
    outputs JSON, dynamic BOOLEAN, PRIMARY KEY(run, parent_drv, child_drv));
CREATE TABLE activities(run VARCHAR, id UBIGINT, parent UBIGINT, type INTEGER,
    text BLOB, drv VARCHAR, machine VARCHAR, phase BLOB, status VARCHAR,
    start_elapsed_ns BIGINT, stop_elapsed_ns BIGINT, PRIMARY KEY(run, id));
CREATE TABLE logs("offset" UBIGINT PRIMARY KEY, run VARCHAR, seq UBIGINT,
    activity UBIGINT, elapsed_ns BIGINT, bytes BLOB, kind VARCHAR);
CREATE INDEX log_cursor ON logs(run, seq);
COMMIT;
)SQL");
  }
  auto version = rows("SELECT schema_version FROM campaign_meta");
  if (version.size() != 1 || version[0].at("schema_version") != 1)
    throw std::runtime_error("unsupported campaign schema version");
  watermark_ =
      rows("SELECT coalesce(max(\"offset\"),0) AS watermark FROM events")[0].at(
          "watermark");
}

void Dataset::exec(const std::string &sql) {
  auto result = connection_.Query(sql);
  if (result->HasError())
    throw std::runtime_error(result->GetError());
}

json Dataset::rows(const std::string &sql) {
  auto result = connection_.Query("SELECT to_json(q) FROM (" + sql + ") q");
  if (result->HasError())
    throw std::runtime_error(result->GetError());
  auto output = json::array();
  for (duckdb::idx_t i = 0; i < result->RowCount(); ++i)
    output.push_back(json::parse(result->GetValue(0, i).ToString()));
  return output;
}

void Dataset::append(const json &batch) {
  if (batch.empty())
    return;
  auto run = batch[0].at("run").get<std::string>();
  auto projection = projections_[run];
  auto next_seq = projection.summary().at("events").get<std::uint64_t>() + 1;
  auto offset = watermark_;
  exec("BEGIN");
  try {
    for (const auto &event : batch) {
      if (event.at("run") != run || event.at("seq") != next_seq++ ||
          (event.at("seq") == 1 && event.at("kind") != "run.requested"))
        throw std::runtime_error("invalid append ordering");
      auto r = quote(run);
      auto seq = event.at("seq").dump();
      auto wall = event.at("wall_ns").dump();
      auto elapsed = event.at("elapsed_ns").dump();
      auto kind = event.at("kind").get<std::string>();
      const auto &p = event.at("payload");
      auto off = std::to_string(++offset);
      exec("INSERT INTO events VALUES (" + off + "," + r + "," + seq + "," +
           wall + "," + elapsed + "," + quote(kind) + "," + quote(p.dump()) +
           "::JSON)");
      projection.apply(event);
      if (kind == "run.requested") {
        exec("INSERT INTO runs VALUES (" + r + "," +
             quote(p.at("drv").get<std::string>()) + "," +
             quote(p.at("store").get<std::string>()) + "," +
             quote(p.value("name", "")) + ",''," + wall + "," + off +
             ", '{}'::JSON)");
      } else if (kind == "recipe.resolved") {
        exec("UPDATE runs SET name=" + quote(p.at("name").get<std::string>()) +
             ",system=" + quote(p.at("system").get<std::string>()) +
             " WHERE run=" + r);
      } else if (kind == "recipe.discovered") {
        auto drv = quote(p.at("drv").get<std::string>());
        exec("INSERT INTO recipes VALUES (" + r + "," + drv + "," +
             quote(p.at("name").get<std::string>()) + "," +
             quote(p.at("system").get<std::string>()) + ")");
        for (const auto &input : p.at("inputs"))
          exec("INSERT INTO edges VALUES (" + r + "," + drv + "," +
               quote(input.at("drv").get<std::string>()) + "," +
               quote(input.at("outputs").dump()) + "::JSON," +
               input.at("dynamic").dump() + ")");
      } else if (kind == "nix.activity-started") {
        exec("INSERT INTO activities VALUES (" + r + "," + id(p, "id") + "," +
             id(p, "parent") + "," + p.at("type").dump() + "," +
             blob(p.at("text_hex")) + "," + quote(p.value("drv", "")) + "," +
             quote(p.value("machine", "")) + ",from_hex(''),'running'," +
             elapsed + ",NULL)");
      } else if (kind == "nix.activity-stopped") {
        exec("UPDATE activities SET status='awaiting-result',"
             "stop_elapsed_ns=" +
             elapsed + " WHERE run=" + r + " AND id=" + id(p, "id"));
      } else if (kind == "nix.result" && p.at("type") == 104 &&
                 !p.at("fields").empty() &&
                 p.at("fields")[0].contains("string_hex")) {
        // Nix 2.34's resSetPhase; raw typed records remain in events.
        exec("UPDATE activities SET phase=" +
             blob(p.at("fields")[0].at("string_hex")) + " WHERE run=" + r +
             " AND id=" + id(p, "id"));
      }
      std::string bytes;
      bool output = false;
      if (p.contains("text_hex") &&
          (kind == "nix.message" || kind == "nix.error" ||
           kind == "nix.stdout" || kind == "worker.error")) {
        bytes = p.at("text_hex");
        output = true;
      } else if (kind == "nix.result" && p.value("build_output", false)) {
        bytes = p.at("fields")[0].at("string_hex");
        output = true;
      }
      if (output)
        exec("INSERT INTO logs VALUES (" + off + "," + r + "," + seq + "," +
             (p.contains("id") ? id(p, "id") : "NULL") + "," + elapsed + "," +
             blob(bytes) + "," + quote(kind) + ")");
    }
    exec("UPDATE runs SET summary=" + quote(projection.summary().dump()) +
         "::JSON,last_offset=" + std::to_string(offset) +
         " WHERE run=" + quote(run));
    exec("COMMIT");
  } catch (...) {
    exec("ROLLBACK");
    throw;
  }
  projections_[run] = std::move(projection);
  watermark_ = offset;
}

std::string Dataset::select_run(std::string run) {
  if (!run.empty())
    return run;
  auto latest = rows("SELECT run FROM runs ORDER BY start_wall_ns DESC, "
                     "last_offset DESC LIMIT 1");
  return latest.empty() ? "" : latest[0].at("run").get<std::string>();
}

json Dataset::summary(std::string run) {
  run = select_run(std::move(run));
  auto found = rows("SELECT summary FROM runs WHERE run=" + quote(run));
  if (found.empty())
    throw std::runtime_error("unknown run: " + run);
  return found[0].at("summary");
}

json Dataset::events(std::string run, std::uint64_t after) {
  run = select_run(std::move(run));
  return rows("SELECT 1 AS version,* FROM events WHERE run=" + quote(run) +
              " AND seq>" + std::to_string(after) + " ORDER BY seq LIMIT 512");
}

json Dataset::logs(std::string run, std::string activity, std::uint64_t after,
                   bool tail) {
  run = select_run(std::move(run));
  auto filter = "run=" + quote(run);
  if (!activity.empty())
    filter += " AND activity::VARCHAR=" + quote(activity);
  auto sql = "SELECT seq,elapsed_ns,coalesce(activity::VARCHAR,'') AS activity,"
             "lower(hex(bytes)) AS bytes_hex FROM logs WHERE " +
             filter;
  if (tail)
    sql = "SELECT * FROM (" + sql +
          " ORDER BY seq DESC LIMIT 200) t ORDER BY seq";
  else
    sql += " AND seq>" + std::to_string(after) + " ORDER BY seq LIMIT 256";
  return rows(sql);
}

json Dataset::view(std::string run, std::string activity, bool detail) {
  run = select_run(std::move(run));
  auto filter = " WHERE run=" + quote(run);
  auto request = rows("SELECT payload FROM events" + filter + " AND seq=1");
  json cohort = nullptr;
  std::string session_filter;
  if (!request.empty() && request[0].at("payload").contains("cohort")) {
    cohort = request[0].at("payload").at("cohort");
    session_filter = " WHERE json_extract_string(e.payload,'$.cohort.id')=" +
                     quote(cohort.at("id").get<std::string>());
  }
  auto sessions =
      rows("SELECT r.run,r.drv,r.name,r.system,r.start_wall_ns,"
           "r.summary,json_object('index',json_extract(e.payload,'$.index'),"
           "'cohort',json_object('id',json_extract(e.payload,'$.cohort.id'))) "
           "AS request FROM runs r LEFT JOIN "
           "events e ON e.run=r.run AND e.seq=1 " +
           session_filter +
           " ORDER BY r.start_wall_ns DESC,r.last_offset DESC LIMIT 256");
  json session = nullptr;
  for (auto &item : sessions) {
    auto state = item.at("summary");
    item.erase("summary");
    item.update(state);
    if (item.at("run") == run)
      session = item;
  }
  // A selected older run may lie outside the bounded sidebar.
  if (session.is_null() && !run.empty()) {
    auto found = rows("SELECT run,drv,name,system,start_wall_ns,summary "
                      "FROM runs WHERE run=" +
                      quote(run));
    if (!found.empty()) {
      session = found[0];
      auto state = session.at("summary");
      session.erase("summary");
      session.update(state);
    }
  }
  json activities = json::array(), output = json::array(),
       time = json::array({{{"elapsed", 0}}}), phases = json::array(),
       failures = json::array();
  // Overview/rail reads do not query or materialize a selected graph or log.
  if (detail) {
    activities = rows(
        "SELECT id::VARCHAR AS id,parent::VARCHAR AS parent,"
        "type,lower(hex(text)) AS text_hex,drv,machine,lower(hex(phase)) AS "
        "phase_hex,status,start_elapsed_ns,stop_elapsed_ns FROM activities" +
        filter + " ORDER BY start_elapsed_ns,id LIMIT 2000");
    for (auto &item : activities) {
      for (auto key : {"text", "phase"}) {
        // Render valid UTF-8; byte-exact strings remain in BLOB columns.
        auto bytes =
            unhex(item.at(std::string(key) + "_hex").get<std::string>());
        json value = bytes;
        item[key] = json::parse(
            value.dump(-1, ' ', false, json::error_handler_t::replace));
      }
    }
    output = logs(run, activity, 0, true);
    time = rows("SELECT coalesce(max(elapsed_ns),0) AS elapsed FROM events" +
                filter);
    phases = rows(
        "SELECT seq,elapsed_ns,json_extract_string(payload,'$.id') AS activity,"
        "json_extract_string(payload,'$.fields[0].string_hex') AS phase_hex "
        "FROM events" +
        filter +
        " AND kind='nix.result' AND "
        "json_extract_string(payload,'$.type')='104' AND "
        "json_extract_string(payload,'$.fields[0].string_hex') IS NOT NULL "
        "ORDER BY seq DESC LIMIT "
        "256");
    std::reverse(phases.begin(), phases.end());
    for (auto &phase : phases) {
      auto bytes = unhex(phase.at("phase_hex").get<std::string>());
      phase["phase"] = json::parse(
          json(bytes).dump(-1, ' ', false, json::error_handler_t::replace));
    }
    failures = rows(
        "SELECT kind,payload FROM events" + filter +
        " AND kind IN ('nix.build-result','worker.error','run.recorder-error',"
        "'run.limit-reached','run.cancel-requested') ORDER BY seq DESC LIMIT "
        "8");
  }
  if (!cohort.is_null()) {
    auto members =
        " FROM runs r JOIN events e ON e.run=r.run AND e.seq=1 WHERE "
        "json_extract_string(e.payload,'$.cohort.id')=" +
        quote(cohort.at("id").get<std::string>());
    auto summaries = rows("SELECT r.summary" + members);
    unsigned completed = 0, succeeded = 0, failed = 0, timed_out = 0;
    for (const auto &item : summaries) {
      const auto &state = item.at("summary");
      if (!state.at("complete").get<bool>())
        continue;
      ++completed;
      auto outcome = state.at("outcome").get<std::string>();
      if (outcome == "built" || outcome == "already-valid" ||
          outcome == "substituted" || outcome == "resolves-to-already-valid")
        ++succeeded;
      else if (outcome == "timed-out")
        ++timed_out;
      else
        ++failed;
    }
    auto finished = rows("SELECT f.payload FROM events f JOIN events e ON "
                         "e.run=f.run AND e.seq=1 "
                         "WHERE f.kind='cohort.finished' AND "
                         "json_extract_string(e.payload,'$.cohort.id')=" +
                         quote(cohort.at("id").get<std::string>()) +
                         " ORDER BY f.\"offset\" DESC LIMIT 1");
    cohort["attempted"] = summaries.size();
    cohort["completed"] = completed;
    cohort["succeeded"] = succeeded;
    cohort["failed"] = failed;
    cohort["timed_out"] = timed_out;
    cohort["unattempted"] = cohort.at("roots").size() - summaries.size();
    cohort["stop_reason"] =
        finished.empty() ? json("") : finished[0].at("payload").at("reason");
  }
  return {{"watermark", watermark_},
          {"cohort", cohort},
          {"sessions", sessions},
          {"session", session},
          {"recipes", detail ? rows("SELECT drv,name,system FROM recipes" +
                                    filter + " ORDER BY drv")
                             : json::array()},
          {"edges",
           detail
               ? rows("SELECT parent_drv,child_drv,outputs,dynamic FROM edges" +
                      filter + " ORDER BY parent_drv,child_drv")
               : json::array()},
          {"activities", activities},
          {"phases", phases},
          {"failure_events", failures},
          {"logs", output},
          {"cursor", output.empty() ? json(0) : output.back().at("seq")},
          {"elapsed_now_ns", time[0].at("elapsed")},
          {"live", false}};
}

json Dataset::export_to(const std::string &directory) {
  auto path = std::filesystem::absolute(directory);
  if (!std::filesystem::create_directory(path))
    throw std::runtime_error("export destination already exists");
  const std::vector<std::string> tables{"events", "runs",       "recipes",
                                        "edges",  "activities", "logs"};
  json manifest = {
      {"schema_version", 1}, {"watermark", watermark_}, {"tables", tables}};
  try {
    exec("BEGIN");
    for (const auto &table : tables)
      exec("COPY " + table + " TO " +
           quote((path / (table + ".parquet")).string()) +
           " (FORMAT PARQUET, COMPRESSION ZSTD)");
    exec("COMMIT");
    // Publication marker is last: a directory without it is not an archive.
    std::ofstream file{path / "manifest.json", std::ios::binary};
    file << manifest.dump(2) << '\n';
    file.close();
    if (!file)
      throw std::runtime_error("write archive manifest failed");
  } catch (...) {
    connection_.Query("ROLLBACK");
    std::filesystem::remove_all(path); // Only the newly-owned destination.
    throw;
  }
  return manifest;
}

} // namespace campaign

#include "dataset.hh"

#include <filesystem>
#include <fstream>
#include <set>

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

duckdb::DBConfig *configure(duckdb::DBConfig &config) {
  // Host RAM is not the service's cgroup allowance. Leave room inside the
  // 4 GiB service for the worker, JSON, HTTP and DuckDB's unmanaged memory.
  config.SetOptionByName("memory_limit", duckdb::Value("1 GiB"));
  config.SetOptionByName("threads", duckdb::Value(2));
  return &config;
}

} // namespace

Dataset::Dataset(const std::string &path, bool writable)
    : database_(open_path(path, writable), configure(config_)),
      connection_(database_) {
  // The application owns this database in one process. Offline commands
  // never append; opening normally also permits DuckDB's WAL recovery.
  auto tables = rows("SELECT table_name FROM information_schema.tables "
                     "WHERE table_schema='main'");
  if (tables.empty() && writable) {
    exec(R"SQL(
BEGIN;
CREATE TABLE campaign_meta(schema_version INTEGER);
INSERT INTO campaign_meta VALUES (2);
-- The single writer validates contiguous run seqs and assigns offsets in
-- the transaction. Large ART indexes do not help our ordered window scans.
CREATE TABLE events("offset" UBIGINT NOT NULL, run VARCHAR, seq UBIGINT,
    wall_ns BIGINT, elapsed_ns BIGINT, kind VARCHAR, payload JSON);
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
CREATE TABLE logs("offset" UBIGINT NOT NULL, run VARCHAR, seq UBIGINT,
    activity UBIGINT, elapsed_ns BIGINT, bytes BLOB, kind VARCHAR);
COMMIT;
)SQL");
  }
  auto version = rows("SELECT schema_version FROM campaign_meta");
  if (version.size() != 1 || (version[0].at("schema_version") != 1 &&
                              version[0].at("schema_version") != 2))
    throw std::runtime_error("unsupported campaign schema version");
  schema_version_ = version[0].at("schema_version");
  watermark_ =
      rows("SELECT coalesce(max(\"offset\"),0) AS watermark FROM events")[0].at(
          "watermark");
  // Rebuild the small overview cache once, also for v1 archives. Keep raw
  // journals authoritative and avoid rewriting a multi-gigabyte recording.
  // Duration scans only fixed-width columns; JSON is read only for the few
  // metadata event kinds. No dashboard request joins against the journal.
  exec(R"SQL(
CREATE TEMP TABLE run_info AS
SELECT r.run, d.duration_ns, m.request, m.cause_hex, m.native_status, m.finished
FROM runs r LEFT JOIN
 (SELECT run, arg_max(elapsed_ns, seq) AS duration_ns FROM events GROUP BY run) d
 ON d.run=r.run LEFT JOIN
 (SELECT run,
   arg_min(payload,seq) FILTER (WHERE kind='run.requested') AS request,
   arg_min(json_extract_string(payload,'$.text_hex'),seq)
     FILTER (WHERE kind='nix.message' AND json_extract(payload,'$.level')=0)
     AS cause_hex,
   arg_max_null(json_extract_string(payload,'$.result.status'),seq)
     FILTER (WHERE kind='nix.build-result') AS native_status,
   arg_max(payload,seq) FILTER (WHERE kind='cohort.finished') AS finished
  FROM events WHERE kind IN
    ('run.requested','nix.message','nix.build-result','cohort.finished')
  GROUP BY run) m ON m.run=r.run;
CREATE UNIQUE INDEX run_info_identity ON run_info(run);
)SQL");
}

void Dataset::exec(const std::string &sql) {
  auto result = connection_.Query(sql);
  if (result->HasError())
    throw std::runtime_error(result->GetError());
}

json Dataset::resources() {
  return {
      {"settings",
       rows("SELECT current_setting('memory_limit') AS memory_limit, "
            "current_setting('threads') AS threads")},
      {"memory", rows("SELECT tag,memory_usage_bytes,temporary_storage_bytes "
                      "FROM duckdb_memory() WHERE memory_usage_bytes>0 OR "
                      "temporary_storage_bytes>0")}};
}

json Dataset::publication_outputs() {
  std::set<std::string> paths;
  for (const auto &row : rows("SELECT summary FROM runs")) {
    const auto &state = row.at("summary");
    auto outcome = state.value("outcome", "incomplete");
    if (!state.value("complete", false) ||
        (outcome != "built" && outcome != "already-valid" &&
         outcome != "substituted" && outcome != "resolves-to-already-valid"))
      continue;
    for (const auto &output : state.at("outputs"))
      if (output.value("valid", false))
        paths.insert(output.at("path").get<std::string>());
  }
  return {{"watermark", watermark_}, {"paths", paths}};
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
        exec("INSERT INTO run_info VALUES (" + r + "," + elapsed + "," +
             quote(p.dump()) + "::JSON,NULL,NULL,NULL)");
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
      if (kind == "nix.message" && p.value("level", -1) == 0)
        exec("UPDATE run_info SET cause_hex=" +
             quote(p.at("text_hex").get<std::string>()) + " WHERE run=" + r +
             " AND cause_hex IS NULL");
      if (kind == "nix.build-result") {
        auto status =
            p.value("result", json::object()).value("status", json(nullptr));
        exec("UPDATE run_info SET native_status=" +
             (status.is_null() ? "NULL" : quote(status.get<std::string>())) +
             " WHERE run=" + r);
      }
      if (kind == "cohort.finished")
        exec("UPDATE run_info SET finished=" + quote(p.dump()) +
             "::JSON WHERE run=" + r);
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
    exec("UPDATE run_info SET duration_ns=" +
         batch.back().at("elapsed_ns").dump() + " WHERE run=" + quote(run));
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
                   bool tail, std::uint64_t before) {
  run = select_run(std::move(run));
  auto filter = "run=" + quote(run);
  if (!activity.empty())
    filter += " AND l.activity::VARCHAR=" + quote(activity);
  // The activity's derivation name labels rows; ids remain copyable.
  auto sql =
      "SELECT l.seq,l.elapsed_ns,coalesce(l.activity::VARCHAR,'') AS "
      "activity,coalesce((SELECT r.name FROM activities a JOIN recipes r "
      "ON r.run=a.run AND r.drv=a.drv WHERE a.run=l.run AND "
      "a.id=l.activity),'') AS activity_name,lower(hex(l.bytes)) AS "
      "bytes_hex FROM logs l WHERE l." +
      filter;
  if (before)
    sql = "SELECT * FROM (" + sql + " AND l.seq<" + std::to_string(before) +
          " ORDER BY l.seq DESC LIMIT " + std::to_string(log_earlier_rows) +
          ") t ORDER BY seq";
  else if (tail)
    sql = "SELECT * FROM (" + sql + " ORDER BY l.seq DESC LIMIT " +
          std::to_string(log_tail_rows) + ") t ORDER BY seq";
  else
    sql += " AND l.seq>" + std::to_string(after) + " ORDER BY seq LIMIT 256";
  return rows(sql);
}

json Dataset::view(std::string run, std::string activity, bool detail) {
  run = select_run(std::move(run));
  auto filter = " WHERE run=" + quote(run);
  auto request = rows("SELECT request AS payload FROM run_info" + filter);
  json cohort = nullptr;
  std::string session_filter;
  if (!request.empty() && request[0].at("payload").contains("cohort")) {
    cohort = request[0].at("payload").at("cohort");
    session_filter = " WHERE json_extract_string(e.request,'$.cohort.id')=" +
                     quote(cohort.at("id").get<std::string>());
  }
  const std::string progress = "e.duration_ns,e.cause_hex";
  auto sessions = rows(
      "SELECT r.run,r.drv,r.name,r.system,r.start_wall_ns,"
      "r.summary," +
      progress +
      ",(SELECT lower(hex(a.phase)) FROM activities a WHERE "
      "a.run=r.run AND a.drv=r.drv ORDER BY a.start_elapsed_ns DESC LIMIT 1) "
      "AS phase_hex,e.native_status,"
      "json_object('index',json_extract(e.request,'$.index'),"
      "'cohort',json_object('id',json_extract(e.request,'$.cohort.id'))) "
      "AS request FROM runs r LEFT JOIN "
      "run_info e ON e.run=r.run " +
      session_filter +
      " ORDER BY r.start_wall_ns DESC,r.last_offset DESC LIMIT " +
      std::string(cohort.is_null() ? "256" : "1024"));
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
    auto found =
        rows("SELECT r.run,r.drv,r.name,r.system,r.start_wall_ns,"
             "r.summary," +
             progress +
             " FROM runs r LEFT JOIN run_info e ON e.run=r.run WHERE r.run=" +
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
       failures = json::array(), errors = json::array();
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
    time = rows("SELECT coalesce(max(duration_ns),0) AS elapsed FROM run_info" +
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
    errors =
        rows("SELECT seq,elapsed_ns,json_extract_string(payload,'$.text_hex') "
             "AS bytes_hex FROM events" +
             filter +
             " AND kind IN ('nix.error','nix.message') AND "
             "json_extract(payload,'$.level')=0 ORDER BY seq DESC LIMIT 4");
  }
  if (!cohort.is_null()) {
    auto members = " FROM runs r JOIN run_info e ON e.run=r.run WHERE "
                   "json_extract_string(e.request,'$.cohort.id')=" +
                   quote(cohort.at("id").get<std::string>());
    auto summaries = rows("SELECT r.summary" + members);
    unsigned completed = 0, succeeded = 0, failed = 0, timed_out = 0, built = 0;
    bool recorder_error = false;
    for (const auto &item : summaries) {
      const auto &state = item.at("summary");
      if (!state.at("complete").get<bool>())
        continue;
      ++completed;
      auto outcome = state.at("outcome").get<std::string>();
      recorder_error |= outcome == "recorder-error";
      if (outcome == "built" || outcome == "already-valid" ||
          outcome == "substituted" || outcome == "resolves-to-already-valid") {
        ++succeeded;
        built += outcome == "built";
      } else if (outcome == "timed-out")
        ++timed_out;
      else
        ++failed;
    }
    auto finished =
        rows("SELECT e.finished AS payload" + members +
             " AND e.finished IS NOT NULL ORDER BY r.last_offset DESC LIMIT 1");
    cohort["attempted"] = summaries.size();
    cohort["completed"] = completed;
    cohort["incomplete"] = summaries.size() - completed;
    cohort["succeeded"] = succeeded;
    cohort["built"] = built;
    cohort["already_valid"] = succeeded - built;
    cohort["failed"] = failed;
    cohort["timed_out"] = timed_out;
    cohort["unattempted"] = cohort.at("roots").size() - summaries.size();
    cohort["stop_reason"] =
        finished.empty() ? json(recorder_error ? "recorder-error" : "")
                         : finished[0].at("payload").at("reason");
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
          {"reported_errors", errors},
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
  json manifest = {{"schema_version", schema_version_},
                   {"watermark", watermark_},
                   {"tables", tables}};
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

#include "catalog.hh"
#include "sql.hh"

#include <set>

namespace campaign {
namespace {

using sql::quote;

duckdb::DBConfig *configure(duckdb::DBConfig &config) {
  config.SetOptionByName("memory_limit", duckdb::Value("256 MiB"));
  config.SetOptionByName("threads", duckdb::Value(1));
  return &config;
}

std::string literal(const json &value) {
  if (value.is_null())
    return "NULL";
  if (value.is_string())
    return quote(value.get<std::string>());
  if (value.is_boolean())
    return value.get<bool>() ? "true" : "false";
  if (value.is_number())
    return value.dump();
  return quote(value.dump()) + "::JSON";
}

const std::set<std::string> campaign_columns{
    "kind",        "name",        "label",       "source",   "revision",
    "options",     "manifest",    "extras",      "recording", "policy",
    "priority",    "state",       "created_ns",  "started_ns", "finished_ns",
    "used_ns",     "stop_reason", "duplicate_of", "fingerprint"};

const std::set<std::string> attempt_columns{
    "finished_ns", "note",       "outcome", "native_status", "wall_ns",
    "build_ns",    "machine",    "failed_drv", "phase",       "error",
    "cause",       "counts",     "outputs"};

constexpr const char *success_outcomes =
    "('built','already-valid','substituted','resolves-to-already-valid')";

} // namespace

Catalog::Catalog(const std::string &path)
    : database_(path, configure(config_)), connection_(database_) {
  if (rows("SELECT table_name FROM information_schema.tables WHERE "
           "table_schema='main' AND table_name='campaigns'")
          .empty())
    exec(R"SQL(
BEGIN;
CREATE TABLE catalog_meta(version INTEGER);
INSERT INTO catalog_meta VALUES (1);
CREATE TABLE campaigns(id VARCHAR PRIMARY KEY, kind VARCHAR, name VARCHAR,
    label VARCHAR, source VARCHAR, revision VARCHAR, options JSON,
    manifest VARCHAR, extras JSON, recording VARCHAR, policy JSON,
    priority INTEGER, state VARCHAR, created_ns BIGINT, started_ns BIGINT,
    finished_ns BIGINT, used_ns BIGINT, stop_reason VARCHAR,
    duplicate_of VARCHAR, fingerprint VARCHAR);
-- No keys on rows the service updates: DuckDB checks uniqueness eagerly.
CREATE TABLE roots(campaign VARCHAR, idx INTEGER, name VARCHAR, drv VARCHAR,
    tags JSON, requires JSON, meta JSON, state VARCHAR);
CREATE TABLE attempts(campaign VARCHAR, name VARCHAR, attempt INTEGER,
    run VARCHAR, drv VARCHAR, started_ns BIGINT, finished_ns BIGINT,
    load1 DOUBLE, in_flight INTEGER, note VARCHAR, outcome VARCHAR,
    native_status VARCHAR, wall_ns BIGINT, build_ns BIGINT, machine VARCHAR,
    failed_drv VARCHAR, phase VARCHAR, error VARCHAR, cause VARCHAR,
    counts JSON, outputs JSON);
COMMIT;
)SQL");
  if (rows("SELECT version FROM catalog_meta")[0].at("version") != 1)
    throw std::runtime_error("unsupported catalog version");
}

void Catalog::exec(const std::string &query) { sql::exec(connection_, query); }
json Catalog::rows(const std::string &query) {
  return sql::rows(connection_, query);
}

json Catalog::campaigns(bool all) {
  auto ok = std::string(success_outcomes);
  return rows(
      "WITH latest AS (SELECT campaign,name,outcome,wall_ns FROM attempts "
      "QUALIFY row_number() OVER (PARTITION BY campaign,name ORDER BY "
      "attempt DESC)=1) SELECT c.id,c.kind,c.name,c.label,c.source,"
      "c.revision,c.options,c.policy,c.priority,c.state,c.created_ns,"
      "c.started_ns,c.finished_ns,c.used_ns,c.stop_reason,c.duplicate_of,"
      "c.manifest,c.recording,count(r.name) AS roots,"
      "count(*) FILTER (WHERE r.state='settled' AND l.outcome IN " +
      ok +
      ") AS succeeded,"
      "count(*) FILTER (WHERE r.state='settled' AND l.outcome='built') AS "
      "built,"
      "count(*) FILTER (WHERE r.state='settled' AND l.outcome IN ('failed',"
      "'worker-error','recorder-error')) AS failed,"
      "count(*) FILTER (WHERE r.state='settled' AND l.outcome='timed-out') "
      "AS timed_out,"
      "count(*) FILTER (WHERE r.state='settled' AND l.outcome IN "
      "('cancelled','incomplete')) AS interrupted,"
      "count(*) FILTER (WHERE r.state='settled' AND l.outcome='skipped') AS "
      "skipped,"
      "count(*) FILTER (WHERE r.state='running') AS running,"
      "count(*) FILTER (WHERE r.state='pending') AS pending,"
      "count(*) FILTER (WHERE r.state='unattempted') AS unattempted,"
      "coalesce(sum(l.wall_ns) FILTER (WHERE r.state='settled'),0) AS "
      "root_ns FROM campaigns c LEFT JOIN roots r ON r.campaign=c.id LEFT "
      "JOIN latest l ON l.campaign=r.campaign AND l.name=r.name" +
      std::string(all ? "" : " WHERE c.duplicate_of IS NULL") +
      " GROUP BY ALL ORDER BY c.created_ns DESC");
}

json Catalog::campaign(const std::string &id) {
  auto found = rows("SELECT * FROM campaigns WHERE id=" + quote(id));
  if (found.empty())
    throw std::runtime_error("unknown campaign: " + id);
  return found[0];
}

json Catalog::roots(const std::string &id) {
  return rows(
      "WITH latest AS (SELECT * FROM attempts WHERE campaign=" + quote(id) +
      " QUALIFY row_number() OVER (PARTITION BY name ORDER BY attempt "
      "DESC)=1) SELECT r.idx,r.name,r.drv,r.tags,r.requires,r.meta,r.state,"
      "l.attempt,l.run,l.started_ns,l.finished_ns,l.load1,l.in_flight,l.note,"
      "l.outcome,l.native_status,l.wall_ns,l.build_ns,l.machine,l.failed_drv,"
      "l.phase,l.error,l.cause,l.counts FROM roots r LEFT JOIN latest l ON "
      "l.name=r.name WHERE r.campaign=" +
      quote(id) + " ORDER BY r.idx");
}

json Catalog::attempts(const std::string &id) {
  return rows("SELECT * EXCLUDE (campaign) FROM attempts WHERE campaign=" +
              quote(id) + " ORDER BY started_ns,name,attempt");
}

json Catalog::restore() {
  return {
      {"campaigns", rows("SELECT * FROM campaigns ORDER BY created_ns")},
      {"roots",
       rows("SELECT r.campaign,r.idx,r.name,r.drv,r.tags,r.requires,r.state,"
            "(SELECT count(*) FROM attempts a WHERE a.campaign=r.campaign "
            "AND a.name=r.name) AS attempts,(SELECT a.outcome FROM attempts "
            "a WHERE a.campaign=r.campaign AND a.name=r.name ORDER BY "
            "a.attempt DESC LIMIT 1) AS outcome FROM roots r JOIN campaigns "
            "c ON c.id=r.campaign WHERE c.state<>'historical' ORDER BY "
            "r.campaign,r.idx")},
      {"open", rows("SELECT a.campaign,a.name,a.attempt,a.run FROM attempts "
                    "a JOIN campaigns c ON c.id=a.campaign WHERE a.outcome "
                    "IS NULL AND c.state<>'historical'")}};
}

std::string Catalog::campaign_of_run(const std::string &run) {
  auto found = rows("SELECT campaign FROM attempts WHERE run=" + quote(run) +
                    " LIMIT 1");
  return found.empty() ? "" : found[0].at("campaign").get<std::string>();
}

std::string Catalog::find_fingerprint(const std::string &fingerprint) {
  auto found = rows("SELECT id FROM campaigns WHERE duplicate_of IS NULL "
                    "AND fingerprint=" +
                    quote(fingerprint) + " LIMIT 1");
  return found.empty() ? "" : found[0].at("id").get<std::string>();
}

json Catalog::publication_outputs() {
  std::set<std::string> paths;
  auto found = rows(
      "SELECT a.outputs FROM attempts a JOIN campaigns c ON c.id=a.campaign "
      "WHERE coalesce(json_extract(c.policy,'$.publish')::BOOLEAN,false) AND "
      "a.outcome IN " +
      std::string(success_outcomes));
  for (const auto &row : found)
    if (row.at("outputs").is_array())
      for (const auto &output : row.at("outputs"))
        if (output.value("valid", false))
          paths.insert(output.at("path").get<std::string>());
  auto count = rows("SELECT count(*) AS n FROM attempts WHERE outcome IS "
                    "NOT NULL")[0]
                   .at("n");
  return {{"watermark", count}, {"paths", paths}};
}

void Catalog::insert_campaign(const json &campaign, const json &roots) {
  exec("BEGIN");
  try {
    std::string columns = "id", values = literal(campaign.at("id"));
    for (const auto &[key, value] : campaign.items()) {
      if (key == "id")
        continue;
      if (!campaign_columns.contains(key))
        throw std::runtime_error("unknown campaign column " + key);
      columns += "," + key;
      values += "," + literal(value);
    }
    exec("INSERT INTO campaigns(" + columns + ") VALUES (" + values + ")");
    for (const auto &root : roots)
      exec("INSERT INTO roots VALUES (" + literal(campaign.at("id")) + "," +
           literal(root.at("idx")) + "," + literal(root.at("name")) + "," +
           literal(root.at("drv")) + "," +
           literal(root.value("tags", json::array())) + "," +
           literal(root.value("requires", json::array())) + "," +
           literal(root.value("meta", json::object())) + "," +
           literal(root.value("state", "pending")) + ")");
    exec("COMMIT");
  } catch (...) {
    connection_.Query("ROLLBACK");
    throw;
  }
}

void Catalog::update_campaign(const std::string &id, const json &fields) {
  std::string assignments;
  for (const auto &[key, value] : fields.items()) {
    if (!campaign_columns.contains(key))
      throw std::runtime_error("unknown campaign column " + key);
    assignments += (assignments.empty() ? "" : ",") + key + "=" +
                   literal(value);
  }
  if (!assignments.empty())
    exec("UPDATE campaigns SET " + assignments + " WHERE id=" + quote(id));
}

void Catalog::set_root_state(const std::string &id, const std::string &name,
                             const std::string &state) {
  exec("UPDATE roots SET state=" + quote(state) + " WHERE campaign=" +
       quote(id) + " AND name=" + quote(name));
}

void Catalog::insert_attempt(const json &a) {
  exec("INSERT INTO attempts(campaign,name,attempt,run,drv,started_ns,load1,"
       "in_flight,note,outcome) VALUES (" +
       literal(a.at("campaign")) + "," + literal(a.at("name")) + "," +
       literal(a.at("attempt")) + "," + literal(a.value("run", json())) + "," +
       literal(a.at("drv")) + "," + literal(a.at("started_ns")) + "," +
       literal(a.value("load1", json())) + "," +
       literal(a.value("in_flight", json())) + "," +
       literal(a.value("note", json())) + "," +
       literal(a.value("outcome", json())) + ")");
}

void Catalog::finish_attempt(const std::string &id, const std::string &name,
                             int attempt, const json &result) {
  std::string assignments;
  for (const auto &[key, value] : result.items())
    if (attempt_columns.contains(key))
      assignments += (assignments.empty() ? "" : ",") + key + "=" +
                     literal(value);
  exec("UPDATE attempts SET " + assignments + " WHERE campaign=" + quote(id) +
       " AND name=" + quote(name) + " AND attempt=" + std::to_string(attempt));
}

} // namespace campaign

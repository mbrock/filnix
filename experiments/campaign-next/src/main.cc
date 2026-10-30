#include "analysis.hh"
#include "catalog.hh"
#include "dataset.hh"
#include "web.hh"

#include <nxtrt/app.hpp>
#include <nxtrt/blocking.hpp>
#include <nxtrt/http-server.hpp>
#include <nxtrt/net.hpp>
#include <nxtrt/subprocess.hpp>

#include <array>
#include <charconv>
#include <cmath>
#include <csignal>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <list>
#include <map>
#include <set>
#include <spawn.h>
#include <sstream>
#include <sys/random.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/syscall.h>
#include <sys/wait.h>

extern char **environ;

using namespace std::chrono_literals;
using campaign::json;

namespace {

volatile std::sig_atomic_t requested_signal = 0;
void request_stop(int signal) { requested_signal = signal; }

void display(const json &event, int fd) {
  const auto &kind = event.at("kind");
  const auto &payload = event.at("payload");
  std::string text;
  if (payload.contains("text_hex") &&
      (kind == "nix.message" || kind == "nix.error" || kind == "nix.stdout" ||
       kind == "worker.error"))
    text = campaign::unhex(payload.at("text_hex").get<std::string>());
  else if (kind == "nix.result" && payload.value("build_output", false))
    text = campaign::unhex(
        payload.at("fields").at(0).at("string_hex").get<std::string>());
  else if (kind == "run.requested" || kind == "run.finished" ||
           kind == "nix.build-result" || kind == "run.cancel-requested" ||
           kind == "recipe.resolved")
    text = kind.get<std::string>() + " " + payload.dump();
  else
    return;
  std::ostringstream prefix;
  prefix << '[' << std::fixed << std::setprecision(3)
         << event.at("elapsed_ns").get<double>() / 1e9 << "] ";
  campaign::write_all(fd, prefix.str() + text + "\n");
}

// FLAGS go to the worker (rebuild, direct); NIX_CONFIG_EXTRA is appended
// to the inherited NIX_CONFIG as the worker's per-client Nix settings.
nxtrt::piped_child spawn_worker(const std::string &drv,
                                const std::string &store,
                                const std::string &flags = "",
                                const std::string &nix_config_extra = "") {
  // Only fd 3 carries the event protocol. stdout/stderr remain ordinary
  // diagnostics, so a runtime diagnostic cannot corrupt the event pipe.
  int pipe[2];
  if (::pipe2(pipe, O_CLOEXEC) != 0)
    throw campaign::system_error("pipe");
  nxt::unique_fd reader{pipe[0]}, writer{pipe[1]};
  auto worker = std::filesystem::read_symlink("/proc/self/exe").parent_path() /
                "filnix-nix-worker";
  auto executable = worker.string();
  auto parent = std::to_string(::getpid());
  std::vector<char *> argv{
      executable.data(),
      const_cast<char *>(drv.c_str()),
      const_cast<char *>(store.c_str()),
      parent.data(),
  };
  if (!flags.empty())
    argv.push_back(const_cast<char *>(flags.c_str()));
  argv.push_back(nullptr);
  std::vector<std::string> variables;
  std::string config;
  for (char **e = environ; *e; ++e) {
    if (std::string_view(*e).starts_with("NIX_CONFIG="))
      config = std::string(*e).substr(11);
    else
      variables.emplace_back(*e);
  }
  if (!nix_config_extra.empty())
    config += (config.empty() || config.ends_with('\n') ? "" : "\n") +
              nix_config_extra;
  if (!config.empty())
    variables.push_back("NIX_CONFIG=" + config);
  std::vector<char *> envp;
  for (auto &v : variables)
    envp.push_back(v.data());
  envp.push_back(nullptr);
  posix_spawn_file_actions_t actions;
  int error = ::posix_spawn_file_actions_init(&actions);
  if (error)
    throw std::runtime_error(std::strerror(error));
  error = ::posix_spawn_file_actions_addclose(&actions, reader.get());
  if (!error)
    error = ::posix_spawn_file_actions_adddup2(&actions, writer.get(), 3);
  if (!error && writer.get() != 3)
    error = ::posix_spawn_file_actions_addclose(&actions, writer.get());
  pid_t pid = -1;
  if (!error)
    error = ::posix_spawn(&pid, executable.c_str(), &actions, nullptr,
                          argv.data(), envp.data());
  ::posix_spawn_file_actions_destroy(&actions);
  if (error)
    throw std::runtime_error("spawn worker: " +
                             std::string(std::strerror(error)));
  int pidfd = ::syscall(SYS_pidfd_open, pid, 0);
  if (pidfd < 0) {
    auto failure = campaign::system_error("pidfd_open");
    ::kill(pid, SIGKILL);
    while (::waitpid(pid, nullptr, 0) < 0 && errno == EINTR) {
    }
    throw failure;
  }
  return {
      .pid = pid, .handle = nxt::unique_fd{pidfd}, .output = std::move(reader)};
}

struct Session;

// One service campaign as the scheduler sees it. The catalog is its
// durable record; this mirrors it for decisions made on the deck.
struct RootState {
  std::size_t idx = 0;
  std::string name, drv, state = "pending", outcome;
  std::vector<std::string> needs;
  int attempts = 0;
};

struct Campaign {
  std::string id, kind, name, state, recording, stop_reason;
  json policy = json::object(), cohort = nullptr;
  std::int64_t priority = 0, created_ns = 0, started_ns = 0, finished_ns = 0,
               used_ns = 0, running_since = 0;
  std::vector<RootState> roots;
  std::map<std::string, std::size_t> by_name;
  // Open while the campaign runs or has roots in flight; owned by the
  // writer pool's thread like every Dataset.
  std::unique_ptr<campaign::Dataset> writer;
  bool opening = false;
  unsigned in_flight = 0;
  std::map<std::string, Session *> sessions;
  std::map<std::string, std::string> running; // run -> root name

  std::int64_t policy_int(const char *key) const {
    return policy.value(key, std::int64_t(0));
  }
};

struct Application {
  // Writers (the catalog and running recordings). Commits must be admitted
  // in the order their events were numbered: capacity is never reached.
  nxtrt::blocking_pool workers{1, 1024};
  // Readers of recordings not being written, analysis and subprocesses, so
  // opening a large archive never delays capture.
  nxtrt::blocking_pool readers{1, 1024};
  std::unique_ptr<campaign::Dataset> data;
  std::map<std::string, std::string> assets;
  std::map<std::string, std::int64_t> live; // run -> monotonic start
  std::string live_run;                     // latest, for single recordings
  bool admitting = false;

  // Service state.
  std::unique_ptr<campaign::Catalog> catalog;
  std::filesystem::path state;
  std::string store = "daemon";
  std::map<std::string, Campaign> campaigns;
  bool promoting = false;
  // Open read-only recordings, most recent first; touched only on `readers`.
  std::list<std::pair<std::string, std::unique_ptr<campaign::Dataset>>>
      cache;
};

struct Session {
  Application &app;
  campaign::Dataset *data;
  std::string run;
  std::int64_t start = campaign::monotonic_ns();
  std::uint64_t seq = 0;
  nxtrt::piped_child child;
  bool done = false, reaped = false, cancel = false;
  nxtrt::child_result exit{};

  Session(Application &application, campaign::Dataset *dataset,
          std::string identity)
      : app(application), data(dataset), run(std::move(identity)) {}

  json event(std::string kind, json payload) {
    return {{"version", 1},
            {"run", run},
            {"seq", ++seq},
            {"wall_ns", campaign::wall_ns()},
            {"elapsed_ns", campaign::monotonic_ns() - start},
            {"kind", std::move(kind)},
            {"payload", std::move(payload)}};
  }

  nxtrt::task<void> commit(json batch) {
    // A commit may have side effects even if its waiter is cancelled.
    // Do not let blocking_pool discard its acknowledgement.
    co_await nxtrt::shield(app.workers.run(
        [data = data, batch = std::move(batch)] { data->append(batch); }));
  }

  nxtrt::task<void> append(std::string kind, json payload) {
    auto batch = json::array();
    batch.push_back(event(std::move(kind), std::move(payload)));
    co_await commit(std::move(batch));
  }
};

nxtrt::task<void> capture(Session &session) {
  std::exception_ptr failure;
  try {
    std::array<std::byte, 64 * 1024> buffer;
    std::string pending;
    while (auto count = co_await nxtrt::op::read_some{session.child.output_fd(),
                                                      buffer}) {
      pending.append(reinterpret_cast<const char *>(buffer.data()), count);
      std::size_t consumed = 0;
      auto batch = json::array();
      while (true) {
        auto end = pending.find('\n', consumed);
        if (end == std::string::npos)
          break;
        if (end - consumed + 1 > campaign::max_record_bytes)
          throw std::runtime_error("worker event exceeds 8 MiB");
        auto event =
            json::parse(pending.begin() + consumed, pending.begin() + end);
        auto payload = event.at("payload");
        payload["capture"] = {
            {"wall_ns", event.at("captured_wall_ns")},
            {"mono_ns", event.at("captured_mono_ns")},
        };
        batch.push_back(session.event(event.at("kind"), std::move(payload)));
        consumed = end + 1;
      }
      pending.erase(0, consumed);
      if (pending.size() > campaign::max_record_bytes)
        throw std::runtime_error("worker event exceeds 8 MiB");
      if (!batch.empty())
        co_await session.commit(std::move(batch));
    }
    if (!pending.empty())
      throw std::runtime_error("worker event stream has a torn final record");
    // Drain output BEFORE acknowledging process completion.
    session.exit = co_await nxtrt::subprocess::wait_child(session.child);
    session.reaped = true;
  } catch (...) {
    failure = std::current_exception();
  }
  session.done = true;
  if (failure)
    std::rethrow_exception(failure);
}

nxtrt::task<void> monitor(Session &session, std::int64_t deadline) {
  std::optional<std::chrono::steady_clock::time_point> stopping;
  while (!session.done) {
    if (!stopping &&
        (requested_signal || session.cancel ||
         (deadline && campaign::monotonic_ns() >= deadline))) {
      bool cancel = requested_signal || session.cancel;
      json payload = {{"signal", requested_signal ? requested_signal : SIGINT}};
      if (session.cancel && !requested_signal)
        payload["operator"] = true;
      co_await session.append(cancel ? "run.cancel-requested"
                                     : "run.limit-reached",
                              std::move(payload));
      co_await nxtrt::subprocess::signal_child(session.child, SIGINT);
      stopping = std::chrono::steady_clock::now();
    }
    if (stopping && std::chrono::steady_clock::now() - *stopping > 2s)
      co_await nxtrt::subprocess::signal_child(session.child, SIGKILL);
    co_await nxtrt::op::timeout::after(100ms);
  }
}

std::string random_id() {
  std::array<char, 16> random;
  if (::getrandom(random.data(), random.size(), 0) !=
      static_cast<ssize_t>(random.size()))
    throw campaign::system_error("getrandom");
  return campaign::hex({random.data(), random.size()});
}

struct RecordOptions {
  std::string run, flags, nix_config;
  json request = json::object();
  std::int64_t deadline = 0;
  std::map<std::string, Session *> *sessions = nullptr;
};

nxtrt::task<int> record(Application &app, campaign::Dataset *data,
                        std::string drv, std::string store,
                        RecordOptions options = {}) {
  Session session{app, data,
                  options.run.empty() ? random_id() : options.run};
  auto request = std::move(options.request);
  request["drv"] = drv;
  request["store"] = store;
  co_await session.append("run.requested", std::move(request));
  app.live[session.run] = session.start;
  app.live_run = session.run;
  if (options.sessions)
    (*options.sessions)[session.run] = &session;
  std::exception_ptr failure;
  try {
    session.child = spawn_worker(drv, store, options.flags, options.nix_config);
    co_await nxtrt::when_all(capture(session),
                             monitor(session, options.deadline));
  } catch (...) {
    failure = std::current_exception();
  }
  if (!session.reaped && session.child.pid > 0) {
    session.exit = co_await nxtrt::shield(
        nxtrt::subprocess::terminate_and_wait(session.child));
    session.reaped = true;
  }
  if (options.sessions)
    options.sessions->erase(session.run);
  std::exception_ptr recorded;
  try {
    if (failure) {
      std::string error;
      try {
        std::rethrow_exception(failure);
      } catch (const std::exception &e) {
        error = e.what();
      }
      json payload = {{"text_hex", campaign::hex(error)}};
      co_await session.append("run.recorder-error", std::move(payload));
    }
    json finish = {
        {"exited", session.exit.exited},
        {"exit_code", session.exit.exit_code},
        {"signaled", session.exit.signaled},
        {"signal", session.exit.signal},
    };
    co_await session.append("run.finished", std::move(finish));
  } catch (...) {
    recorded = std::current_exception();
  }
  app.live.erase(session.run);
  if (app.live_run == session.run)
    app.live_run = app.live.empty() ? "" : app.live.begin()->first;
  if (recorded)
    std::rethrow_exception(recorded);
  auto summary = co_await app.workers.run(
      [data, run = session.run] { return data->summary(run); });
  std::cout << summary.dump() << std::endl;
  if (failure)
    std::rethrow_exception(failure);
  co_return session.exit.exited ? session.exit.exit_code
                                : 128 + session.exit.signal;
}

nxtrt::task<void> replay(Application &app, std::string run, double speed,
                         bool raw) {
  std::uint64_t after = 0;
  auto start = std::chrono::steady_clock::now();
  std::optional<std::int64_t> first;
  while (true) {
    auto batch = co_await app.workers.run(
        [&app, run, after] { return app.data->events(run, after); });
    if (batch.empty())
      break;
    for (const auto &event : batch) {
      auto elapsed = event.at("elapsed_ns").get<std::int64_t>();
      if (!first)
        first = elapsed;
      if (speed > 0) {
        double seconds = static_cast<double>(elapsed - *first) / 1e9 / speed;
        if (!std::isfinite(seconds) || seconds > 1e9)
          throw std::runtime_error("replay delay is too large");
        auto target =
            start + std::chrono::duration_cast<std::chrono::nanoseconds>(
                        std::chrono::duration<double>{seconds});
        if (auto delay = target - std::chrono::steady_clock::now(); delay > 0ns)
          co_await nxtrt::op::timeout::after(delay);
      }
      if (raw)
        campaign::write_all(STDOUT_FILENO, event.dump() + "\n");
      else
        display(event, STDOUT_FILENO);
      after = event.at("seq");
    }
  }
}

std::string decode(std::string_view input) {
  std::string value;
  for (std::size_t i = 0; i < input.size(); ++i) {
    char c = input[i];
    if (c == '%') {
      unsigned byte;
      if (i + 2 >= input.size())
        throw std::runtime_error("bad percent encoding");
      auto result =
          std::from_chars(input.data() + i + 1, input.data() + i + 3, byte, 16);
      if (result.ec != std::errc{} || result.ptr != input.data() + i + 3)
        throw std::runtime_error("bad percent encoding");
      c = static_cast<char>(byte);
      i += 2;
    } else if (c == '+')
      c = ' ';
    if (!c)
      throw std::runtime_error("NUL in query parameter");
    value += c;
  }
  return value;
}

using nxtrt::http::response;

response reply(int status, std::string body,
               std::string type = "application/json") {
  return response{status,
                  {{"Content-Type", type},
                   {"Cache-Control", "no-store"},
                   {"X-Content-Type-Options", "nosniff"}},
                  std::move(body),
                  {}};
}

response redirect(std::string location) {
  return response{302, {{"Location", std::move(location)}}, "", {}};
}

bool is_success(const std::string &outcome) {
  return outcome == "built" || outcome == "already-valid" ||
         outcome == "substituted" || outcome == "resolves-to-already-valid";
}

struct Query {
  std::string path;
  std::map<std::string, std::string> params;
  std::uint64_t after = 0, before = 0;
  std::string raw;
};

Query parse_query(const std::string &target) {
  Query q;
  auto question = target.find('?');
  q.path = target.substr(0, question);
  if (question != std::string::npos) {
    q.raw = target.substr(question + 1);
    auto query = std::string_view(q.raw);
    while (!query.empty()) {
      auto end = query.find('&');
      auto item = query.substr(0, end);
      auto equal = item.find('=');
      if (equal != std::string_view::npos)
        q.params[decode(item.substr(0, equal))] =
            decode(item.substr(equal + 1));
      if (end == std::string_view::npos)
        break;
      query.remove_prefix(end + 1);
    }
  }
  for (auto [key, target] :
       {std::pair{"after", &q.after}, std::pair{"before", &q.before}})
    if (q.params.contains(key)) {
      auto &v = q.params.at(key);
      auto result = std::from_chars(v.data(), v.data() + v.size(), *target);
      if (result.ec != std::errc{} || result.ptr != v.data() + v.size())
        throw std::runtime_error("invalid cursor");
    }
  return q;
}

const std::set<std::string> viewer_paths{
    "/",        "/overview", "/state",     "/logs",
    "/graph",   "/sessions", "/api/state", "/api/logs"};

struct ViewContext {
  json cohort = nullptr;       // a service campaign's roots, else recorded
  bool watch = false;          // admitting or recording now
  std::string follow;          // the run `follow` opens
  json extra = json::object(); // merged into the view (service facts)
};

// The single-recording viewer: overview, session state, graph and logs.
// GET selects the recording; `get` returns its Dataset on `pool`'s thread.
template <class Get>
nxtrt::task<response> viewer(Application &app, nxtrt::blocking_pool &pool,
                             Get get, Query q, ViewContext ctx) {
  const auto &path = q.path;
  auto requested_run = q.params["run"], activity = q.params["activity"];
  auto run = requested_run.empty() ? ctx.follow : requested_run;
  bool is_logs = path == "/logs" || path == "/api/logs";
  bool detail =
      path == "/api/state" || path == "/state" || path == "/graph" ||
      (path == "/" && (!requested_run.empty() || q.params["follow"] == "1"));
  json result = co_await pool.run([get, run, activity, after = q.after,
                                   before = q.before, is_logs, detail,
                                   cohort = ctx.cohort,
                                   tail = q.params["tail"] == "1"] {
    campaign::Dataset &data = get();
    return is_logs ? data.logs(run, activity, after, tail, before)
                   : data.view(run, activity, detail, cohort);
  });
  if (!is_logs) {
    result["live_run"] = ctx.follow;
    result["live_runs"] = json::array();
    for (const auto &[id, _] : app.live)
      result["live_runs"].push_back(id);
    result["watch"] = ctx.watch;
    result.update(ctx.extra);
    auto &cohort = result["cohort"];
    if (!ctx.watch && cohort.is_object() &&
        cohort.value("incomplete", 0u) &&
        cohort.value("stop_reason", "").empty())
      cohort["stop_reason"] = "recording-interrupted";
  }
  if (!is_logs && result.at("session").is_object()) {
    auto id = result["session"]["run"].get<std::string>();
    bool live =
        app.live.contains(id) && !result["session"]["complete"].get<bool>();
    result["live"] = live;
    if (live)
      result["elapsed_now_ns"] = campaign::monotonic_ns() - app.live.at(id);
  }
  bool api = path.starts_with("/api/");
  auto body =
      api                ? result.dump()
      : is_logs          ? campaign::web_logs(result, run, activity,
                                     q.params["tail"] == "1" ? 0 : q.after,
                                     q.before)
      : path == "/state" ? campaign::web_state(result, requested_run, activity)
      : path == "/graph"
          ? campaign::web_graph(result, run, q.after, q.params["node"])
      : path == "/sessions"
          ? campaign::web_sessions(result, run, q.params["filter"],
                                   q.params["find"], q.after)
      : path == "/overview"
          ? campaign::web_overview(result)
          : campaign::web_page(result, requested_run, activity,
                               q.params["follow"] == "1" &&
                                   requested_run.empty());
  co_return reply(200, std::move(body),
                  api ? "application/json" : "text/html; charset=utf-8");
}

std::optional<response> asset(Application &app, const std::string &path) {
  auto name = path.substr(path.rfind('/'));
  if (!app.assets.contains(name))
    return std::nullopt;
  return response{200,
                  {{"Content-Type", name.ends_with(".css") ? "text/css"
                                                           : "text/javascript"},
                   {"X-Content-Type-Options", "nosniff"}},
                  app.assets.at(name),
                  {}};
}

// ---------------------------------------------------------------- policy

json default_policy() {
  return {{"parallel_roots", 1},     {"max_jobs", 2},
          {"cores", 4},              {"builders", "default"},
          {"max_silent_time", 1800}, {"build_timeout", 0},
          {"root_timeout", 7200},    {"budget", 86400},
          {"rebuild", false},        {"graph", "full"},
          {"retry_infrastructure", 1}, {"publish", true}};
}

json merge_policy(json policy, const json &changes) {
  for (const auto &[key, value] : changes.items()) {
    if (!policy.contains(key))
      throw std::runtime_error("unknown policy setting " + key);
    if (policy.at(key).is_number_integer()) {
      if (!value.is_number_integer() || value.get<std::int64_t>() < 0 ||
          value.get<std::int64_t>() > 7 * 86400)
        throw std::runtime_error("policy " + key +
                                 " must be a nonnegative integer");
    } else if (policy.at(key).is_boolean()) {
      if (!value.is_boolean())
        throw std::runtime_error("policy " + key + " must be a boolean");
    } else if (!value.is_string())
      throw std::runtime_error("policy " + key + " must be a string");
    policy[key] = value;
  }
  auto bounded = [&](const char *key, std::int64_t low, std::int64_t high) {
    auto n = policy.at(key).get<std::int64_t>();
    if (n < low || n > high)
      throw std::runtime_error(std::string("policy ") + key + " must be " +
                               std::to_string(low) + "–" +
                               std::to_string(high));
  };
  bounded("parallel_roots", 1, 32);
  bounded("max_jobs", 0, 64);
  bounded("cores", 0, 64);
  bounded("root_timeout", 1, 7 * 86400);
  bounded("budget", 1, 7 * 86400);
  bounded("retry_infrastructure", 0, 5);
  if (policy.at("builders") != "default" && policy.at("builders") != "local")
    throw std::runtime_error("policy builders must be default or local");
  if (policy.at("graph") != "full" && policy.at("graph") != "direct")
    throw std::runtime_error("policy graph must be full or direct");
  return policy;
}

std::string nix_config(const json &p) {
  std::string c = "max-jobs = " + p.at("max_jobs").dump() + "\ncores = " +
                  p.at("cores").dump() +
                  "\nmax-silent-time = " + p.at("max_silent_time").dump() +
                  "\n";
  if (p.at("build_timeout").get<std::int64_t>() > 0)
    c += "timeout = " + p.at("build_timeout").dump() + "\n";
  if (p.at("builders") == "local")
    c += "builders =\n";
  return c;
}

std::string worker_flags(const json &p) {
  std::string flags;
  if (p.at("rebuild").get<bool>())
    flags += "rebuild";
  if (p.at("graph") == "direct")
    flags += std::string(flags.empty() ? "" : ",") + "direct";
  return flags;
}

double load_average() {
  std::ifstream file{"/proc/loadavg"};
  double load = 0;
  file >> load;
  return load;
}

// --------------------------------------------------------- campaign state

json cohort_of(const Campaign &c) {
  json roots = json::array();
  for (const auto &r : c.roots)
    roots.push_back({{"name", r.name}, {"drv", r.drv}});
  return {{"id", c.id}, {"name", c.name}, {"roots", roots}};
}

nxtrt::task<void> persist(Application &app, const std::string &id,
                          json fields) {
  co_await nxtrt::shield(app.workers.run(
      [&app, id, fields = std::move(fields)] {
        app.catalog->update_campaign(id, fields);
      }));
}

nxtrt::task<void> open_writer(Application &app, Campaign &c) {
  while (c.opening)
    co_await nxtrt::op::timeout::after(20ms);
  if (c.writer)
    co_return;
  c.opening = true;
  std::exception_ptr failure;
  try {
    // A read-only instance of the same file must close first.
    co_await app.readers.run([&app, id = c.id] {
      app.cache.remove_if([&](const auto &item) { return item.first == id; });
    });
    c.writer = co_await app.workers.run([path = c.recording] {
      return std::make_unique<campaign::Dataset>(path, true);
    });
  } catch (...) {
    failure = std::current_exception();
  }
  c.opening = false;
  if (failure)
    std::rethrow_exception(failure);
}

nxtrt::task<void> close_writer_if_idle(Application &app, Campaign &c) {
  if (!c.writer || c.in_flight || c.state == "running" || c.opening)
    co_return;
  c.opening = true;
  auto writer = std::move(c.writer);
  co_await nxtrt::shield(
      app.workers.run([writer = std::move(writer)]() mutable {
        writer.reset();
      }));
  c.opening = false;
}

// The campaign's recording on the thread that owns it, for one call.
template <class Fn>
auto with_recording(Application &app, Campaign &c, Fn fn)
    -> nxtrt::task<std::invoke_result_t<Fn &, campaign::Dataset &>> {
  while (c.opening)
    co_await nxtrt::op::timeout::after(20ms);
  if (c.writer)
    co_return co_await app.workers.run(
        [fn, data = c.writer.get()]() mutable { return fn(*data); });
  co_return co_await app.readers.run(
      [fn, &app, id = c.id, path = c.recording]() mutable {
        auto found = std::find_if(app.cache.begin(), app.cache.end(),
                                  [&](const auto &i) { return i.first == id; });
        if (found == app.cache.end()) {
          // At most two archives open beside the writers.
          while (app.cache.size() >= 2)
            app.cache.pop_back();
          app.cache.emplace_front(
              id, std::make_unique<campaign::Dataset>(path, false, "512 MiB", true));
        } else
          app.cache.splice(app.cache.begin(), app.cache, found);
        return fn(*app.cache.front().second);
      });
}

Campaign &load_campaign(Application &app, const json &row) {
  auto &c = app.campaigns[row.at("id").get<std::string>()];
  c.id = row.at("id");
  auto str = [&](const char *key) {
    return row.contains(key) && row.at(key).is_string()
               ? row.at(key).get<std::string>()
               : std::string();
  };
  auto num = [&](const char *key) {
    return row.contains(key) && row.at(key).is_number()
               ? row.at(key).get<std::int64_t>()
               : std::int64_t(0);
  };
  c.kind = str("kind");
  c.name = str("name");
  c.state = str("state");
  c.recording = str("recording");
  c.stop_reason = str("stop_reason");
  c.policy = row.value("policy", json::object());
  if (c.policy.is_null())
    c.policy = json::object();
  c.priority = num("priority");
  c.created_ns = num("created_ns");
  c.started_ns = num("started_ns");
  c.finished_ns = num("finished_ns");
  c.used_ns = num("used_ns");
  return c;
}

void add_root(Campaign &c, const json &row) {
  RootState r;
  r.idx = row.at("idx").get<std::size_t>();
  r.name = row.at("name");
  r.drv = row.at("drv");
  r.state = row.value("state", "pending");
  if (row.contains("outcome") && row.at("outcome").is_string())
    r.outcome = row.at("outcome");
  r.attempts = row.value("attempts", 0);
  for (const auto &q : row.value("requires", json::array()))
    r.needs.push_back(q);
  c.by_name[r.name] = c.roots.size();
  c.roots.push_back(std::move(r));
}

bool budget_exhausted(const Campaign &c) {
  auto used = c.used_ns + (c.running_since
                               ? campaign::monotonic_ns() - c.running_since
                               : 0);
  return used >= c.policy_int("budget") * 1'000'000'000;
}

// ---------------------------------------------------------------- scheduler

nxtrt::task<Campaign *> active(Application &app) {
  for (auto &[id, c] : app.campaigns)
    if (c.state == "running")
      co_return &c;
  if (app.promoting)
    co_return nullptr;
  Campaign *best = nullptr;
  for (auto &[id, c] : app.campaigns)
    if (c.state == "queued" &&
        (!best || c.priority > best->priority ||
         (c.priority == best->priority && c.created_ns < best->created_ns)))
      best = &c;
  if (!best)
    co_return nullptr;
  app.promoting = true;
  std::exception_ptr failure;
  try {
    co_await open_writer(app, *best);
    if (best->state == "queued") {
      best->state = "running";
      best->running_since = campaign::monotonic_ns();
      if (!best->started_ns)
        best->started_ns = campaign::wall_ns();
      best->stop_reason.clear();
      co_await persist(app, best->id,
                       {{"state", "running"},
                        {"started_ns", best->started_ns},
                        {"stop_reason", nullptr}});
      std::cerr << "campaign " << best->id << " running\n";
    }
  } catch (...) {
    failure = std::current_exception();
  }
  app.promoting = false;
  if (failure)
    std::rethrow_exception(failure);
  co_return best->state == "running" ? best : nullptr;
}

// Leaves the running state: accumulates running time for the budget.
json leave_running(Campaign &c, std::string state) {
  if (c.running_since)
    c.used_ns += campaign::monotonic_ns() - c.running_since;
  c.running_since = 0;
  c.state = std::move(state);
  return {{"state", c.state}, {"used_ns", c.used_ns}};
}

nxtrt::task<bool> maybe_finish(Application &app, Campaign &c) {
  if (c.state != "running" || c.in_flight)
    co_return false;
  bool pending = false;
  for (const auto &r : c.roots)
    pending |= r.state == "pending";
  bool budget = budget_exhausted(c);
  if (pending && !budget)
    co_return false;
  auto fields = leave_running(c, "finished");
  c.finished_ns = campaign::wall_ns();
  c.stop_reason = budget && pending ? "budget-exhausted" : "all-roots-attempted";
  fields["finished_ns"] = c.finished_ns;
  fields["stop_reason"] = c.stop_reason;
  co_await persist(app, c.id, std::move(fields));
  co_await close_writer_if_idle(app, c);
  std::cerr << "campaign " << c.id << " finished: " << c.stop_reason << "\n";
  co_return true;
}

// Claims the next admissible root in manifest order: pending, every
// requirement settled. Roots whose requirement did not succeed are settled
// as skipped.
std::optional<std::size_t> next_root(Campaign &c,
                                     std::vector<std::size_t> &skipped) {
  for (std::size_t i = 0; i < c.roots.size(); ++i) {
    auto &root = c.roots[i];
    if (root.state != "pending")
      continue;
    bool waiting = false, blocked = false;
    for (const auto &name : root.needs) {
      const auto &required = c.roots[c.by_name.at(name)];
      if (required.state != "settled")
        waiting = true;
      else if (!is_success(required.outcome))
        blocked = true;
    }
    if (blocked) {
      root.state = "settled";
      root.outcome = "skipped";
      ++root.attempts;
      skipped.push_back(i);
    } else if (!waiting) {
      // Claimed here, synchronously: an awaited task need not start
      // before another lane looks for work.
      root.state = "running";
      ++root.attempts;
      ++c.in_flight;
      return i;
    }
  }
  return std::nullopt;
}

nxtrt::task<void> run_root(Application &app, Campaign &c, std::size_t k) {
  // next_root claimed it: running, in flight, its attempt counted.
  auto &root = c.roots[k];
  int attempt = root.attempts;
  // A campaign resumed after a restart has no writer until now.
  std::exception_ptr unopened;
  try {
    co_await open_writer(app, c);
  } catch (...) {
    unopened = std::current_exception();
  }
  if (unopened) {
    root.state = "pending";
    --root.attempts;
    --c.in_flight;
    std::rethrow_exception(unopened);
  }
  auto run = random_id();
  auto load = load_average();
  json row = {{"campaign", c.id},          {"name", root.name},
              {"attempt", attempt},        {"run", run},
              {"drv", root.drv},           {"started_ns", campaign::wall_ns()},
              {"load1", load},             {"in_flight", c.in_flight}};
  co_await nxtrt::shield(app.workers.run([&app, row, id = c.id,
                                          name = root.name] {
    app.catalog->insert_attempt(row);
    app.catalog->set_root_state(id, name, "running");
  }));
  c.running[run] = root.name;
  auto now = campaign::monotonic_ns();
  auto budget_end = c.running_since + (c.policy_int("budget") * 1'000'000'000 -
                                       c.used_ns);
  RecordOptions options;
  options.run = run;
  options.flags = worker_flags(c.policy);
  options.nix_config = nix_config(c.policy);
  options.deadline =
      std::min(budget_end, now + c.policy_int("root_timeout") * 1'000'000'000);
  options.sessions = &c.sessions;
  options.request = {{"name", root.name},
                     {"campaign", c.id},
                     {"index", root.idx},
                     {"attempt", attempt},
                     {"cohort", {{"id", c.id}}},
                     {"policy", c.policy},
                     {"load1", load},
                     {"in_flight", c.in_flight},
                     {"budget_seconds", c.policy_int("budget")},
                     {"root_timeout_seconds", c.policy_int("root_timeout")}};
  bool operator_cancel = false;
  json result;
  std::string recorder_error;
  try {
    co_await record(app, c.writer.get(), root.drv, app.store,
                    std::move(options));
  } catch (const std::exception &e) {
    recorder_error = e.what();
  }
  c.running.erase(run);
  operator_cancel = c.state == "cancelled";
  bool stopping = requested_signal;
  try {
    auto facts = co_await app.workers.run(
        [data = c.writer.get(), run] { return data->attempt_facts(run); });
    result = co_await app.readers.run(
        [facts = std::move(facts)] { return campaign::analyze(facts); });
  } catch (const std::exception &e) {
    if (recorder_error.empty())
      recorder_error = e.what();
  }
  if (!recorder_error.empty()) {
    result["outcome"] = "recorder-error";
    result["note"] = recorder_error;
  }
  auto outcome = result.value("outcome", "incomplete");
  if (outcome == "failed" && result.value("native_status", json()) == "TimedOut")
    outcome = result["outcome"] = "timed-out";
  result["finished_ns"] = campaign::wall_ns();
  std::string next = "settled";
  if (stopping && (outcome == "cancelled" || outcome == "incomplete")) {
    result["note"] = "service-stopping";
    next = "pending";
  } else if (operator_cancel && outcome == "cancelled")
    result["note"] = "cancelled by operator";
  else if (outcome == "worker-error" &&
           attempt <= c.policy_int("retry_infrastructure")) {
    result["note"] = "worker error; retrying";
    next = "pending";
  }
  co_await nxtrt::shield(app.workers.run(
      [&app, id = c.id, name = root.name, attempt, result, next] {
        app.catalog->finish_attempt(id, name, attempt, result);
        app.catalog->set_root_state(id, name, next);
      }));
  root.state = next;
  root.outcome = outcome;
  --c.in_flight;
  if (outcome == "recorder-error" && c.state == "running") {
    // Never continue a campaign whose observations may be incomplete.
    auto fields = leave_running(c, "paused");
    c.stop_reason = "recorder-error";
    fields["stop_reason"] = c.stop_reason;
    co_await persist(app, c.id, std::move(fields));
    std::cerr << "campaign " << c.id << " paused: " << recorder_error << "\n";
  }
  co_await close_writer_if_idle(app, c);
}

nxtrt::task<void> lane(Application &app, unsigned index) {
  while (!requested_signal) {
    std::string failure;
    try {
      // No co_await inside && or ||: GCC 15 does not short-circuit it.
      auto *c = co_await active(app);
      bool admit = c != nullptr;
      if (admit)
        admit = !(co_await maybe_finish(app, *c));
      if (admit)
        admit = index < std::uint64_t(c->policy_int("parallel_roots")) &&
                !budget_exhausted(*c);
      if (admit) {
        std::vector<std::size_t> skipped;
        auto k = next_root(*c, skipped);
        for (auto i : skipped) {
          const auto &r = c->roots[i];
          json row = {{"campaign", c->id},
                      {"name", r.name},
                      {"attempt", r.attempts},
                      {"drv", r.drv},
                      {"started_ns", campaign::wall_ns()},
                      {"outcome", "skipped"},
                      {"note", "a required root did not succeed"}};
          co_await nxtrt::shield(app.workers.run([&app, row] {
            app.catalog->insert_attempt(row);
            app.catalog->set_root_state(row.at("campaign"), row.at("name"),
                                        "settled");
          }));
        }
        if (k) {
          co_await run_root(app, *c, *k);
          continue;
        }
      }
    } catch (const std::exception &e) {
      failure = e.what();
    }
    if (!failure.empty()) {
      std::cerr << "scheduler lane " << index << ": " << failure << "\n";
      co_await nxtrt::op::timeout::after(5s);
    } else
      co_await nxtrt::op::timeout::after(250ms);
  }
}

// After a restart: close attempts the service did not see end, and make
// their roots pending again; running campaigns continue.
nxtrt::task<void> restore(Application &app) {
  auto saved = co_await app.workers.run([&app] {
    return app.catalog->restore();
  });
  for (const auto &row : saved.at("campaigns")) {
    auto &c = load_campaign(app, row);
    if (c.state == "running")
      c.running_since = campaign::monotonic_ns();
  }
  for (const auto &row : saved.at("roots"))
    add_root(app.campaigns.at(row.at("campaign")), row);
  for (auto &[id, c] : app.campaigns)
    if (c.state != "historical")
      c.cohort = cohort_of(c);
  for (const auto &open : saved.at("open")) {
    auto &c = app.campaigns.at(open.at("campaign"));
    auto name = open.at("name").get<std::string>();
    int attempt = open.at("attempt");
    auto run = open.value("run", "");
    json result = {{"outcome", "incomplete"}, {"note", "service-crashed"}};
    try {
      co_await open_writer(app, c);
      auto facts = co_await app.workers.run(
          [data = c.writer.get(), run] { return data->attempt_facts(run); });
      if (facts.at("summary").value("complete", false)) {
        result = co_await app.readers.run(
            [facts] { return campaign::analyze(facts); });
        result["note"] = "settled before a restart";
      } else
        result["wall_ns"] = facts.value("duration_ns", json());
    } catch (const std::exception &e) {
      std::cerr << "restore " << c.id << " " << name << ": " << e.what()
                << "\n";
    }
    result["finished_ns"] = campaign::wall_ns();
    bool settled = result.value("note", "") == "settled before a restart";
    co_await app.workers.run([&app, id = c.id, name, attempt, result,
                              settled] {
      app.catalog->finish_attempt(id, name, attempt, result);
      app.catalog->set_root_state(id, name, settled ? "settled" : "pending");
    });
    auto &root = c.roots[c.by_name.at(name)];
    root.state = settled ? "settled" : "pending";
    root.outcome = result.value("outcome", "incomplete");
  }
  for (auto &[id, c] : app.campaigns) {
    for (auto &root : c.roots)
      if (root.state == "running") {
        root.state = "pending";
        co_await app.workers.run([&app, id = c.id, name = root.name] {
          app.catalog->set_root_state(id, name, "pending");
        });
      }
    co_await close_writer_if_idle(app, c);
  }
}

// ----------------------------------------------------------------- admin

std::string slug_of(std::string s) {
  std::string out;
  for (char c : s) {
    if (std::isalnum(static_cast<unsigned char>(c)) || c == '.' || c == '_' ||
        c == '-')
      out += static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    else if (!out.empty() && out.back() != '-')
      out += '-';
  }
  while (!out.empty() && (out.back() == '-' || out.back() == '.'))
    out.pop_back();
  if (out.empty() || out.size() > 96)
    throw std::runtime_error("campaign id must be 1–96 characters of "
                             "[a-z0-9._-]");
  return out;
}

std::string unique_id(Application &app, std::string base) {
  auto id = base;
  for (int n = 2; app.campaigns.contains(id); ++n)
    id = base + "-" + std::to_string(n);
  return id;
}

std::string today() {
  auto t = std::time(nullptr);
  std::tm tm{};
  ::gmtime_r(&t, &tm);
  char buffer[32];
  std::strftime(buffer, sizeof buffer, "%Y%m%d-%H%M", &tm);
  return buffer;
}

json read_json_file(const std::string &path) {
  std::ifstream file{path};
  if (!file)
    throw std::runtime_error("cannot read " + path);
  return json::parse(file);
}

// Validates a frozen manifest's roots; returns catalog root rows.
json manifest_roots(const json &manifest) {
  if (!manifest.at("roots").is_array() || manifest.at("roots").empty() ||
      manifest.at("roots").size() > 1024)
    throw std::runtime_error("a manifest needs 1–1024 roots");
  json roots = json::array();
  std::set<std::string> names;
  for (std::size_t i = 0; i < manifest.at("roots").size(); ++i) {
    const auto &root = manifest.at("roots")[i];
    if (!root.at("name").is_string() || !root.at("drv").is_string() ||
        root.at("name").get<std::string>().empty() ||
        !root.at("drv").get<std::string>().starts_with("/") ||
        !root.at("drv").get<std::string>().ends_with(".drv") ||
        names.contains(root.at("name")))
      throw std::runtime_error("invalid root " + root.dump().substr(0, 200));
    auto needs = root.value("requires", json::array());
    for (const auto &r : needs)
      if (!r.is_string() || !names.contains(r))
        throw std::runtime_error("root " + root.at("name").get<std::string>() +
                                 " requires an earlier root, not " + r.dump());
    auto tags = root.value("tags", json::array());
    for (const auto &t : tags)
      if (!t.is_string())
        throw std::runtime_error("tags must be strings");
    names.insert(root.at("name"));
    roots.push_back({{"idx", i},
                     {"name", root.at("name")},
                     {"drv", root.at("drv")},
                     {"tags", tags},
                     {"requires", needs},
                     {"meta", root.value("meta", json::object())}});
  }
  return roots;
}

json manifest_extras(const json &manifest) {
  json extras = json::object();
  for (const auto *key : {"excluded", "set_aside", "selection", "select"})
    if (manifest.contains(key))
      extras[key] = manifest.at(key);
  return extras;
}

std::string str(const json &j, const char *key, std::string fallback = "") {
  return j.contains(key) && j.at(key).is_string() ? j.at(key).get<std::string>()
                                                  : fallback;
}

// Roots a store manifest beside the campaign (an indirect GC root).
void add_gc_root(const std::string &store, const std::string &path,
                 const std::filesystem::path &link) {
  std::vector<std::string> args{"nix-store", "--store", store,  "--realise",
                                path,        "--add-root", link.string(),
                                "--indirect"};
  std::vector<char *> argv;
  for (auto &a : args)
    argv.push_back(a.data());
  argv.push_back(nullptr);
  pid_t pid;
  posix_spawn_file_actions_t actions;
  ::posix_spawn_file_actions_init(&actions);
  ::posix_spawn_file_actions_addopen(&actions, STDOUT_FILENO, "/dev/null",
                                     O_WRONLY, 0);
  int error = ::posix_spawnp(&pid, "nix-store", &actions, nullptr,
                             argv.data(), environ);
  ::posix_spawn_file_actions_destroy(&actions);
  if (error)
    throw std::runtime_error("spawn nix-store: " +
                             std::string(std::strerror(error)));
  int status = 0;
  while (::waitpid(pid, &status, 0) < 0 && errno == EINTR) {
  }
  if (!WIFEXITED(status) || WEXITSTATUS(status))
    throw std::runtime_error("nix-store --add-root failed for " + path);
}

nxtrt::task<json> submit(Application &app, json body) {
  auto manifest_path = body.at("manifest").get<std::string>();
  auto manifest = co_await app.readers.run(
      [manifest_path] { return read_json_file(manifest_path); });
  auto roots = manifest_roots(manifest);
  auto policy = merge_policy(default_policy(),
                             body.value("policy", json::object()));
  auto options = manifest.value("options", json::object());
  if (options.empty() && manifest.contains("scope"))
    options = {{"scope", manifest.at("scope")}};
  auto kind = str(manifest, "kind", manifest.contains("scope") ? "world"
                                                               : "roots");
  auto revision = str(manifest, "revision");
  auto base = body.contains("id")
                  ? slug_of(body.at("id"))
                  : slug_of(today() + "-" + kind + "-" +
                            revision.substr(0, 7) +
                            (options.contains("opt")
                                 ? "-" + options.at("opt").get<std::string>()
                                 : "") +
                            (options.contains("scope")
                                 ? "-" + options.at("scope").get<std::string>()
                                 : ""));
  auto id = unique_id(app, base);
  auto directory = app.state / "campaigns" / id;
  std::filesystem::create_directories(directory);
  auto recording = (directory / "recording.duckdb").string();
  auto link = directory / "manifest.json";
  if (manifest_path.starts_with("/nix/store/"))
    co_await app.readers.run([&app, manifest_path, link] {
      add_gc_root(app.store, manifest_path, link);
    });
  else
    std::filesystem::copy_file(manifest_path, link);
  // Create the recording now, so the campaign can be viewed while queued.
  co_await app.workers.run([recording] {
    campaign::Dataset{recording, true};
  });
  json row = {{"id", id},
              {"kind", kind},
              {"name", str(manifest, "name", id)},
              {"label", body.value("label", json())},
              {"source", str(manifest, "source")},
              {"revision", revision},
              {"options", options},
              {"manifest", manifest_path},
              {"extras", manifest_extras(manifest)},
              {"recording", recording},
              {"policy", policy},
              {"priority", body.value("priority", 0)},
              {"state", "queued"},
              {"created_ns", campaign::wall_ns()},
              {"used_ns", 0}};
  co_await app.workers.run(
      [&app, row, roots] { app.catalog->insert_campaign(row, roots); });
  auto &c = load_campaign(app, row);
  for (const auto &r : roots)
    add_root(c, r);
  c.cohort = cohort_of(c);
  std::cerr << "campaign " << id << " queued: " << roots.size() << " roots\n";
  co_return json{{"id", id}, {"roots", roots.size()}, {"state", "queued"}};
}

// Adds an existing recording as a historical campaign, read in place.
nxtrt::task<json> register_recording(Application &app, json body) {
  auto path = std::filesystem::absolute(body.at("path").get<std::string>())
                  .string();
  auto facts = co_await app.readers.run([path] {
    campaign::Dataset data{path, false, "512 MiB", true};
    auto list = data.run_list();
    list["fingerprint"] = data.fingerprint();
    // Logs only for unsuccessful roots: a historical success needs none.
    json attempts = json::array();
    for (const auto &run : list.at("runs")) {
      auto outcome = run.at("summary").value("outcome", "incomplete");
      auto f = data.attempt_facts(run.at("run"));
      if (is_success(outcome))
        f["log_hex"] = json::array();
      auto a = campaign::analyze(f);
      a["run"] = run.at("run");
      attempts.push_back(a);
    }
    list["analysis"] = attempts;
    return list;
  });
  auto fingerprint = facts.at("fingerprint").get<std::string>();
  auto duplicate = co_await app.workers.run([&app, fingerprint] {
    return app.catalog->find_fingerprint(fingerprint);
  });
  json cohort = nullptr;
  std::uint64_t most = 0;
  for (const auto &c : facts.at("cohorts"))
    if (c.at("runs").get<std::uint64_t>() > most) {
      most = c.at("runs");
      cohort = c.at("cohort");
    }
  json manifest = cohort;
  if (body.contains("manifest"))
    manifest = co_await app.readers.run(
        [m = body.at("manifest").get<std::string>()] {
          return read_json_file(m);
        });
  std::int64_t first = 0, last = 0;
  for (const auto &run : facts.at("runs")) {
    auto start = run.at("start_wall_ns").get<std::int64_t>();
    auto end = start + run.value("duration_ns", std::int64_t(0));
    if (!first || start < first)
      first = start;
    last = std::max(last, end);
  }
  auto kind = manifest.is_object() && manifest.contains("scope")
                  ? std::string("world")
                  : manifest.is_object() ? std::string("roots")
                                         : std::string("recording");
  auto revision = manifest.is_object() ? str(manifest, "revision") : "";
  auto base = body.contains("id")
                  ? slug_of(body.at("id"))
                  : slug_of("historical-" + kind + "-" +
                            (revision.empty() ? std::string("pilot")
                                              : revision.substr(0, 7)));
  auto id = unique_id(app, base);
  std::string stop_reason;
  if (!facts.at("finished").empty())
    stop_reason = str(facts.at("finished")[0].at("finished"), "reason");
  json options = json::object();
  if (manifest.is_object() && manifest.contains("scope"))
    options["scope"] = manifest.at("scope");
  json row = {{"id", id},
              {"kind", kind},
              {"name", manifest.is_object() ? str(manifest, "name", id) : id},
              {"label", body.value("label", json(path))},
              {"source", manifest.is_object() ? str(manifest, "source") : ""},
              {"revision", revision},
              {"options", options},
              {"manifest", body.value("manifest", json())},
              {"extras", manifest.is_object() ? manifest_extras(manifest)
                                              : json::object()},
              {"recording", path},
              {"policy", {{"publish", body.value("publish", false)}}},
              {"priority", 0},
              {"state", "historical"},
              {"created_ns", first},
              {"started_ns", first},
              {"finished_ns", last},
              {"used_ns", last - first},
              {"stop_reason", stop_reason},
              {"fingerprint", fingerprint}};
  json roots = json::array(), attempts = json::array();
  if (!duplicate.empty())
    row["duplicate_of"] = duplicate;
  else {
    std::map<std::string, std::size_t> index;
    if (manifest.is_object() && manifest.contains("roots"))
      for (const auto &r : manifest.at("roots")) {
        index[r.at("name")] = roots.size();
        roots.push_back({{"idx", roots.size()},
                         {"name", r.at("name")},
                         {"drv", r.at("drv")},
                         {"state", "unattempted"}});
      }
    std::map<std::string, int> counts;
    auto cohort_id = cohort.is_object() ? str(cohort, "id") : "";
    for (std::size_t i = 0; i < facts.at("runs").size(); ++i) {
      const auto &run = facts.at("runs")[i];
      auto name = str(run, "name", run.at("drv").get<std::string>());
      if (!cohort_id.empty() && str(run, "cohort") != cohort_id)
        continue;
      if (!index.contains(name)) {
        index[name] = roots.size();
        roots.push_back({{"idx", roots.size()},
                         {"name", name},
                         {"drv", run.at("drv")}});
      }
      roots[index.at(name)]["state"] = "settled";
      auto a = facts.at("analysis")[i];
      auto start = run.at("start_wall_ns").get<std::int64_t>();
      a["campaign"] = id;
      a["name"] = name;
      a["attempt"] = ++counts[name];
      a["drv"] = run.at("drv");
      a["started_ns"] = start;
      a["finished_ns"] = start + run.value("duration_ns", std::int64_t(0));
      if (a.at("outcome") == "failed" && a.value("native_status", json()) ==
                                             "TimedOut")
        a["outcome"] = "timed-out";
      attempts.push_back(a);
    }
  }
  co_await app.workers.run([&app, row, roots, attempts] {
    app.catalog->insert_campaign(row, roots);
    for (const auto &a : attempts) {
      app.catalog->insert_attempt(a);
      app.catalog->finish_attempt(a.at("campaign"), a.at("name"),
                                  a.at("attempt"), a);
    }
  });
  load_campaign(app, row);
  co_return json{{"id", id},
                 {"duplicate_of", duplicate.empty() ? json() : json(duplicate)},
                 {"roots", roots.size()},
                 {"attempts", attempts.size()}};
}

// Derives every settled attempt's analysis again from the recording, as
// the current service would; outcomes and notes stay as recorded.
nxtrt::task<json> reanalyze(Application &app, Campaign &c) {
  auto attempts = co_await app.workers.run(
      [&app, id = c.id] { return app.catalog->attempts(id); });
  json updated = json::array();
  for (const auto &a : attempts) {
    if (!a.at("run").is_string() || !a.at("outcome").is_string())
      continue;
    auto facts = co_await with_recording(
        app, c, [run = a.at("run").get<std::string>()](campaign::Dataset &d) {
          return d.attempt_facts(run);
        });
    auto result = co_await app.readers.run(
        [facts = std::move(facts)] { return campaign::analyze(facts); });
    result.erase("outcome");
    co_await app.workers.run([&app, id = c.id, a, result] {
      app.catalog->finish_attempt(id, a.at("name"), a.at("attempt"), result);
    });
    updated.push_back(a.at("run"));
  }
  co_return json{{"id", c.id}, {"reanalyzed", updated.size()}};
}

nxtrt::task<json> control(Application &app, Campaign &c,
                          const std::string &action, const json &body) {
  if (action == "reanalyze")
    co_return co_await reanalyze(app, c);
  if (c.state == "historical")
    throw std::runtime_error("historical campaigns are read-only");
  if (action == "pause") {
    if (c.state != "running" && c.state != "queued")
      throw std::runtime_error("only a queued or running campaign pauses");
    auto fields = leave_running(c, "paused");
    c.stop_reason = "paused by operator";
    fields["stop_reason"] = c.stop_reason;
    co_await persist(app, c.id, fields);
  } else if (action == "resume") {
    if (c.state != "paused")
      throw std::runtime_error("only a paused campaign resumes");
    c.state = "queued";
    c.stop_reason.clear();
    co_await persist(app, c.id, {{"state", "queued"}, {"stop_reason", nullptr}});
  } else if (action == "cancel") {
    if (c.state == "finished" || c.state == "cancelled")
      throw std::runtime_error("campaign already " + c.state);
    auto fields = leave_running(c, "cancelled");
    c.finished_ns = campaign::wall_ns();
    c.stop_reason = "cancelled by operator";
    fields["finished_ns"] = c.finished_ns;
    fields["stop_reason"] = c.stop_reason;
    co_await persist(app, c.id, fields);
    for (auto &[run, session] : c.sessions)
      session->cancel = true;
  } else if (action == "priority") {
    if (!body.contains("priority") || !body.at("priority").is_number_integer())
      throw std::runtime_error("priority needs an integer");
    c.priority = body.at("priority");
    co_await persist(app, c.id, {{"priority", c.priority}});
  } else if (action == "retry") {
    std::set<std::string> names, outcomes;
    for (const auto &n : body.value("roots", json::array()))
      names.insert(n.get<std::string>());
    for (const auto &o : body.value("outcomes", json::array()))
      outcomes.insert(o.get<std::string>());
    if (names.empty() && outcomes.empty())
      outcomes = {"failed",    "timed-out",    "cancelled", "incomplete",
                  "skipped",   "worker-error", "recorder-error"};
    for (const auto &n : names)
      if (!c.by_name.contains(n))
        throw std::runtime_error("no root named " + n);
    json retried = json::array();
    for (auto &root : c.roots)
      if (root.state == "settled" &&
          (names.contains(root.name) || outcomes.contains(root.outcome))) {
        root.state = "pending";
        retried.push_back(root.name);
      }
    co_await app.workers.run([&app, id = c.id, retried] {
      for (const auto &n : retried)
        app.catalog->set_root_state(id, n, "pending");
    });
    if (!retried.empty() && (c.state == "finished" || c.state == "cancelled")) {
      c.state = "queued";
      c.stop_reason.clear();
      co_await persist(app, c.id, {{"state", "queued"},
                                   {"stop_reason", nullptr},
                                   {"finished_ns", nullptr}});
    }
    co_return json{{"id", c.id}, {"retried", retried}, {"state", c.state}};
  } else if (action == "export") {
    auto directory = body.at("directory").get<std::string>();
    auto results = co_await app.workers.run([&app, id = c.id] {
      return json{{"campaign", app.catalog->campaign(id)},
                  {"roots", app.catalog->roots(id)},
                  {"attempts", app.catalog->attempts(id)}};
    });
    auto manifest = co_await with_recording(
        app, c, [directory](campaign::Dataset &d) {
          return d.export_to(directory);
        });
    std::ofstream file{std::filesystem::path(directory) / "results.json"};
    file << results.dump(1) << '\n';
    co_return json{{"id", c.id}, {"directory", directory}, {"archive", manifest}};
  } else
    throw std::runtime_error("unknown action " + action);
  co_await close_writer_if_idle(app, c);
  co_return json{{"id", c.id}, {"state", c.state}, {"priority", c.priority}};
}

nxtrt::task<json> status(Application &app) {
  json in_flight = json::array(), queue = json::array();
  std::string running;
  for (auto &[id, c] : app.campaigns) {
    if (c.state == "running")
      running = id;
    if (c.state == "queued" || c.state == "paused")
      queue.push_back({{"id", id}, {"state", c.state}, {"priority", c.priority}});
    for (const auto &[run, root] : c.running) {
      json item = {{"campaign", id}, {"run", run}, {"root", root}};
      if (app.live.contains(run))
        item["elapsed_ns"] = campaign::monotonic_ns() - app.live.at(run);
      in_flight.push_back(item);
    }
  }
  co_return json{{"running", running.empty() ? json() : json(running)},
                 {"in_flight", in_flight},
                 {"queue", queue},
                 {"load1", load_average()},
                 {"stopping", requested_signal != 0}};
}

Campaign &find_campaign(Application &app, const std::string &id) {
  if (!app.campaigns.contains(id))
    throw std::runtime_error("unknown campaign " + id);
  return app.campaigns.at(id);
}

nxtrt::task<response> admin(Application &app, nxtrt::http::request req) {
  try {
    auto q = parse_query(req.target);
    std::vector<std::string> parts;
    for (std::size_t i = 1; i <= q.path.size();) {
      auto end = q.path.find('/', i);
      if (end == std::string::npos)
        end = q.path.size();
      if (end > i)
        parts.push_back(q.path.substr(i, end - i));
      i = end + 1;
    }
    auto body = req.body.empty() ? json::object() : json::parse(req.body);
    json result;
    if (req.method == "GET" && parts == std::vector<std::string>{"status"})
      result = co_await status(app);
    else if (req.method == "GET" && parts.size() == 1 &&
             parts[0] == "campaigns")
      result = co_await app.workers.run([&app, all = q.params["all"] == "1"] {
        return app.catalog->campaigns(all);
      });
    else if (req.method == "GET" && parts.size() >= 2 &&
             parts[0] == "campaigns") {
      find_campaign(app, parts[1]);
      bool results = parts.size() == 3 && parts[2] == "results";
      if (parts.size() > 3 || (parts.size() == 3 && !results))
        co_return reply(404, json{{"error", "not found"}}.dump());
      result = co_await app.workers.run([&app, id = parts[1], results] {
        json out = {{"campaign", app.catalog->campaign(id)},
                    {"roots", app.catalog->roots(id)}};
        if (results)
          out["attempts"] = app.catalog->attempts(id);
        return out;
      });
    } else if (req.method == "POST" && parts == std::vector<std::string>{
                                                   "campaigns"})
      result = co_await submit(app, body);
    else if (req.method == "POST" && parts == std::vector<std::string>{
                                                   "register"})
      result = co_await register_recording(app, body);
    else if (req.method == "POST" && parts.size() == 3 &&
             parts[0] == "campaigns")
      result = co_await control(app, find_campaign(app, parts[1]), parts[2],
                                body);
    else
      co_return reply(404, json{{"error", "not found"}}.dump());
    co_return reply(200, result.dump());
  } catch (const std::exception &e) {
    co_return reply(400, json{{"error", e.what()}}.dump());
  }
}

// ------------------------------------------------------------ public web

json catalog_extra(Application &, Campaign &c) {
  return {{"service", true},
          {"campaign", {{"id", c.id},
                        {"kind", c.kind},
                        {"state", c.state},
                        {"stop_reason", c.stop_reason}}}};
}

nxtrt::task<response> public_handler(Application &app,
                                     nxtrt::http::request req) {
  if (req.method != "GET" && req.method != "HEAD")
    co_return response{405, {{"Allow", "GET, HEAD"}}, "Read-only viewer\n", {}};
  Query q;
  try {
    q = parse_query(req.target);
  } catch (const std::exception &) {
    co_return response{400, {}, "Invalid query\n", {}};
  }
  if (q.path == "/healthz")
    co_return reply(200, "ok\n", "text/plain");
  if (auto a = asset(app, q.path))
    co_return std::move(*a);
  if (q.path == "/api/outputs")
    co_return reply(200, (co_await app.workers.run([&app] {
                            return app.catalog->publication_outputs();
                          })).dump());
  if (q.path == "/api/campaigns" || (q.path == "/" && q.params["run"].empty() &&
                                     q.params["follow"].empty())) {
    auto list = co_await app.workers.run([&app, all = q.params["all"] == "1"] {
      return app.catalog->campaigns(all);
    });
    if (q.path == "/api/campaigns")
      co_return reply(200, list.dump());
    co_return reply(200, campaign::web_campaigns(list),
                    "text/html; charset=utf-8");
  }
  if (q.path == "/api/resources") {
    json out = json::object();
    for (auto &[id, c] : app.campaigns)
      if (c.writer)
        out[id] = co_await app.workers.run(
            [data = c.writer.get()] { return data->resources(); });
    co_return reply(200, out.dump());
  }
  // Links from the single-campaign viewer: send them to their campaign.
  if (viewer_paths.contains(q.path)) {
    std::string id;
    if (!q.params["run"].empty())
      id = co_await app.workers.run([&app, run = q.params["run"]] {
        return app.catalog->campaign_of_run(run);
      });
    else
      for (auto &[cid, c] : app.campaigns)
        if (c.state == "running")
          id = cid;
    if (id.empty())
      co_return response{404, {}, "Not found\n", {}};
    co_return redirect("/c/" + id + q.path + (q.raw.empty() ? "" : "?" + q.raw));
  }
  if (!q.path.starts_with("/c/"))
    co_return response{404, {}, "Not found\n", {}};
  auto rest = q.path.substr(3);
  auto slash = rest.find('/');
  auto id = rest.substr(0, slash);
  if (!app.campaigns.contains(id))
    co_return response{404, {}, "No such campaign\n", {}};
  if (slash == std::string::npos)
    co_return redirect("/c/" + id + "/" + (q.raw.empty() ? "" : "?" + q.raw));
  auto &c = app.campaigns.at(id);
  q.path = rest.substr(slash);
  if (q.path == "/survey" || q.path == "/api/results") {
    auto results = co_await app.workers.run([&app, id] {
      return json{{"campaign", app.catalog->campaign(id)},
                  {"roots", app.catalog->roots(id)}};
    });
    if (q.path == "/api/results")
      co_return reply(200, results.dump());
    co_return reply(200, campaign::web_survey(results),
                    "text/html; charset=utf-8");
  }
  if (!viewer_paths.contains(q.path))
    co_return response{404, {}, "Not found\n", {}};
  ViewContext ctx;
  ctx.cohort = c.cohort;
  ctx.watch = c.state == "running" || c.in_flight;
  for (const auto &[run, _] : c.sessions)
    ctx.follow = run;
  ctx.extra = catalog_extra(app, c);
  while (c.opening)
    co_await nxtrt::op::timeout::after(20ms);
  if (c.writer)
    co_return co_await viewer(
        app, app.workers,
        [data = c.writer.get()]() -> campaign::Dataset & { return *data; }, q,
        ctx);
  co_return co_await viewer(
      app, app.readers,
      [&app, id = c.id, path = c.recording]() -> campaign::Dataset & {
        auto found = std::find_if(app.cache.begin(), app.cache.end(),
                                  [&](const auto &i) { return i.first == id; });
        if (found == app.cache.end()) {
          while (app.cache.size() >= 2)
            app.cache.pop_back();
          app.cache.emplace_front(
              id, std::make_unique<campaign::Dataset>(path, false, "512 MiB", true));
        } else
          app.cache.splice(app.cache.begin(), app.cache, found);
        return *app.cache.front().second;
      },
      q, ctx);
}

nxt::unique_fd listen_unix(const std::string &path) {
  nxt::unique_fd fd{::socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0)};
  if (fd.get() < 0)
    throw campaign::system_error("socket");
  sockaddr_un address{};
  address.sun_family = AF_UNIX;
  if (path.size() >= sizeof address.sun_path)
    throw std::runtime_error("socket path too long");
  std::memcpy(address.sun_path, path.c_str(), path.size() + 1);
  ::unlink(path.c_str());
  // Only the service user (and root) may administer it.
  auto mask = ::umask(0177);
  int bound = ::bind(fd.get(), reinterpret_cast<sockaddr *>(&address),
                     sizeof address);
  ::umask(mask);
  if (bound != 0)
    throw campaign::system_error("bind " + path);
  if (::listen(fd.get(), 16) != 0)
    throw campaign::system_error("listen");
  return fd;
}

// A single recording (watch, serve): the viewer at the root.
nxtrt::task<response> handle(Application &app, nxtrt::http::request req) {
  if (req.method != "GET" && req.method != "HEAD")
    co_return response{405, {{"Allow", "GET, HEAD"}}, "Read-only viewer\n", {}};
  Query q;
  try {
    q = parse_query(req.target);
  } catch (const std::exception &) {
    co_return response{400, {}, "Invalid query\n", {}};
  }
  if (q.path == "/healthz")
    co_return reply(200, "ok\n", "text/plain");
  if (q.path == "/api/outputs" || q.path == "/api/resources") {
    auto result = co_await app.workers.run([&app, path = q.path] {
      return path == "/api/resources" ? app.data->resources()
                                      : app.data->publication_outputs();
    });
    co_return reply(200, result.dump());
  }
  if (auto a = asset(app, q.path))
    co_return std::move(*a);
  if (!viewer_paths.contains(q.path))
    co_return response{404, {}, "Not found\n", {}};
  ViewContext ctx;
  ctx.watch = app.admitting || !app.live_run.empty();
  ctx.follow = app.live_run;
  co_return co_await viewer(
      app, app.workers,
      [data = app.data.get()]() -> campaign::Dataset & { return *data; }, q,
      ctx);
}

struct Options {
  std::string command, path, drv, store = "daemon", run, directory, socket;
  std::uint16_t port = 8080;
  double speed = 1;
  bool raw = false;
};

nxtrt::task<int> server_body(Application &app, const Options &options) {
  int code = 0;
  if (options.command == "watch") {
    app.admitting = true;
    code = co_await record(app, app.data.get(), options.drv, options.store);
    app.admitting = false;
  }
  while (!requested_signal)
    co_await nxtrt::op::timeout::after(100ms);
  co_return code;
}

nxtrt::task<int> scheduler(Application &app) {
  std::vector<nxtrt::task<void>> lanes;
  for (unsigned i = 0; i < 32; ++i)
    lanes.push_back(lane(app, i));
  co_await nxtrt::settle_range(std::move(lanes));
  co_return 0;
}

nxtrt::task<int> service(Application &app, const Options &options) {
  app.state = std::filesystem::absolute(options.path);
  app.store = options.store;
  std::filesystem::create_directories(app.state / "campaigns");
  co_await app.workers.run([&app] {
    app.catalog = std::make_unique<campaign::Catalog>(
        (app.state / "catalog.duckdb").string());
  });
  co_await restore(app);
  auto listener = nxtrt::net::listen_tcp_loopback(options.port);
  auto socket_path = options.socket.empty()
                         ? (app.state / "admin.sock").string()
                         : options.socket;
  auto admin_listener = listen_unix(socket_path);
  std::cerr << "Listening on http://127.0.0.1:"
            << ntohs(nxtrt::net::socket_address(listener.get()).sin_port)
            << " and " << socket_path << std::endl;
  nxtrt::http::server_options opts;
  opts.max_connections = 8;
  nxtrt::http::server_options admin_opts;
  admin_opts.max_connections = 4;
  auto [body, http, control] = co_await nxtrt::settle(
      std::tuple{scheduler(app),
                 nxtrt::http::serve(
                     listener.get(),
                     [&app](nxtrt::http::request req) {
                       return public_handler(app, std::move(req));
                     },
                     opts),
                 nxtrt::http::serve(
                     admin_listener.get(),
                     [&app](nxtrt::http::request req) {
                       return admin(app, std::move(req));
                     },
                     admin_opts)},
      nxtrt::first_completion_group{});
  ::unlink(socket_path.c_str());
  if (!http)
    std::rethrow_exception(http.error());
  if (!control)
    std::rethrow_exception(control.error());
  if (!body)
    std::rethrow_exception(body.error());
  co_return *body;
}

void load_assets(Application &app) {
  auto assets = std::getenv("CAMPAIGN_STATIC_DIR");
  auto base = assets ? std::filesystem::path(assets)
                     : std::filesystem::read_symlink("/proc/self/exe")
                               .parent_path()
                               .parent_path() /
                           "share/filnix-campaign";
  for (const auto *name : {"htmx.js", "observatory.css", "observatory.js"}) {
    std::ifstream file{base / name, std::ios::binary};
    app.assets[std::string("/") + name].assign(
        std::istreambuf_iterator<char>{file}, {});
  }
  for (const auto &[name, bytes] : app.assets)
    if (bytes.empty())
      throw std::runtime_error("missing viewer asset " + name +
                               "; set CAMPAIGN_STATIC_DIR");
}

nxtrt::task<int> execute(Application &app, const Options &options) {
  if (options.command == "service") {
    load_assets(app);
    co_return co_await service(app, options);
  }
  co_await app.workers.run([&app, path = options.path,
                            writable = options.command == "record" ||
                                       options.command == "watch"] {
    app.data = std::make_unique<campaign::Dataset>(path, writable);
  });
  if (options.command == "record")
    co_return co_await record(app, app.data.get(), options.drv, options.store);
  if (options.command == "watch" || options.command == "serve") {
    load_assets(app);
    auto listener = nxtrt::net::listen_tcp_loopback(options.port);
    std::cerr << "Listening on http://127.0.0.1:"
              << ntohs(nxtrt::net::socket_address(listener.get()).sin_port)
              << std::endl;
    nxtrt::http::server_options opts;
    opts.max_connections = 8;
    // Both tasks are owned until settled. Shutdown drains HTTP handlers
    // before the caller destroys the DuckDB connection/pool.
    auto [body, http] = co_await nxtrt::settle(
        std::tuple{server_body(app, options),
                   nxtrt::http::serve(
                       listener.get(),
                       [&app](nxtrt::http::request req) {
                         return handle(app, std::move(req));
                       },
                       opts)},
        nxtrt::first_completion_group{});
    if (!http)
      std::rethrow_exception(http.error());
    if (!body)
      std::rethrow_exception(body.error());
    co_return *body;
  }
  if (options.command == "replay") {
    // Validate selection even when no events match.
    co_await app.workers.run(
        [&app, run = options.run] { return app.data->summary(run); });
    co_await replay(app, options.run, options.speed, options.raw);
  } else {
    auto output = co_await app.workers.run([&app, options] {
      return options.command == "export"
                 ? app.data->export_to(options.directory)
                 : app.data->summary(options.run);
    });
    std::cout << output.dump() << std::endl;
  }
  co_return 0;
}

nxtrt::task<void> close(Application &app) {
  co_await nxtrt::shield(app.readers.run([&app] { app.cache.clear(); }));
  co_await nxtrt::shield(app.workers.run([&app] {
    app.data.reset();
    for (auto &[id, c] : app.campaigns)
      c.writer.reset();
    app.catalog.reset();
  }));
  co_await app.readers.close();
  co_await app.workers.close();
}

} // namespace

int main(int argc, char **argv) {
  try {
    if (argc < 3)
      throw std::runtime_error(
          "usage: filnix-campaign service STATE-DIRECTORY [--port N] "
          "[--socket PATH] [--store URI]; record|watch DRV DATABASE "
          "[--store URI] [--port N]; serve|inspect|replay DATABASE "
          "[--run ID] [--port N] [--speed N] [--json]; export DATABASE "
          "DIRECTORY");
    Options options;
    options.command = argv[1];
    int i = 2;
    if (options.command == "record" || options.command == "watch") {
      if (argc < 4)
        throw std::runtime_error("build requires DRV and DATABASE");
      options.drv = argv[i++];
    } else if (options.command != "serve" && options.command != "inspect" &&
               options.command != "replay" && options.command != "export" &&
               options.command != "service")
      throw std::runtime_error("unknown command");
    options.path = argv[i++];
    if (options.command == "export") {
      if (i == argc)
        throw std::runtime_error("export requires destination directory");
      options.directory = argv[i++];
    }
    for (; i < argc; ++i) {
      std::string_view flag = argv[i];
      if (flag == "--json" && options.command == "replay") {
        options.raw = true;
        continue;
      }
      if (++i == argc)
        throw std::runtime_error("missing option value");
      std::string value = argv[i];
      if (flag == "--store" &&
          (options.command == "record" || options.command == "watch" ||
           options.command == "service"))
        options.store = value;
      else if (flag == "--socket" && options.command == "service")
        options.socket = value;
      else if (flag == "--run" &&
               (options.command == "inspect" || options.command == "replay"))
        options.run = value;
      else if (flag == "--port" &&
               (options.command == "serve" || options.command == "watch" ||
                options.command == "service")) {
        unsigned n;
        auto result =
            std::from_chars(value.data(), value.data() + value.size(), n);
        if (result.ec != std::errc{} ||
            result.ptr != value.data() + value.size() || n > 65535)
          throw std::runtime_error("invalid port");
        options.port = n;
      } else if (flag == "--speed" && options.command == "replay") {
        std::size_t consumed;
        options.speed = std::stod(value, &consumed);
        if (consumed != value.size() || !std::isfinite(options.speed) ||
            options.speed < 0)
          throw std::runtime_error("speed must be finite and nonnegative");
      } else
        throw std::runtime_error("unexpected option");
    }
    std::signal(SIGINT, request_stop);
    std::signal(SIGTERM, request_stop);
    Application app;
    nxtrt::runtime runtime;
    return runtime.run([&] {
      return nxtrt::finally(execute(app, options),
                            [&app] { return close(app); });
    });
  } catch (const std::exception &error) {
    std::cerr << "filnix-campaign: " << error.what() << '\n';
    return 2;
  }
}

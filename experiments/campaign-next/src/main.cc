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
#include <map>
#include <spawn.h>
#include <sstream>
#include <sys/random.h>
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

nxtrt::piped_child spawn_worker(const std::string &drv,
                                const std::string &store) {
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
  std::array<char *, 5> argv{
      executable.data(),
      const_cast<char *>(drv.c_str()),
      const_cast<char *>(store.c_str()),
      parent.data(),
      nullptr,
  };
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
                          argv.data(), environ);
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
      .pid = pid, .pidfd = nxt::unique_fd{pidfd}, .output = std::move(reader)};
}

struct Application {
  // Eight HTTP callers plus capture/monitor stay below capacity. Producers
  // never wait for admission, so one-worker FIFO preserves assigned seqs.
  nxtrt::blocking_pool workers{1, 16};
  std::unique_ptr<campaign::Dataset> data;
  std::string htmx;
  std::string live_run;
  std::int64_t live_start = 0;
};

struct Session {
  Application &app;
  std::string run;
  std::int64_t start = campaign::monotonic_ns();
  std::uint64_t seq = 0;
  nxtrt::piped_child child;
  bool done = false, reaped = false;
  nxtrt::child_result exit{};

  Session(Application &application, std::string identity)
      : app(application), run(std::move(identity)) {}

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
        [&app = app, batch = std::move(batch)] { app.data->append(batch); }));
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
    if (!stopping && (requested_signal ||
                      (deadline && campaign::monotonic_ns() >= deadline))) {
      json payload = {{"signal", requested_signal ? requested_signal : SIGINT}};
      co_await session.append(requested_signal ? "run.cancel-requested"
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

nxtrt::task<int> record(Application &app, std::string drv, std::string store,
                        json request = json::object(),
                        std::int64_t deadline = 0) {
  std::array<char, 16> random;
  if (::getrandom(random.data(), random.size(), 0) !=
      static_cast<ssize_t>(random.size()))
    throw campaign::system_error("getrandom");
  Session session{app, campaign::hex({random.data(), random.size()})};
  request["drv"] = drv;
  request["store"] = store;
  co_await session.append("run.requested", std::move(request));
  app.live_run = session.run;
  app.live_start = session.start;
  std::exception_ptr failure;
  try {
    session.child = spawn_worker(drv, store);
    // These lambdas are factories, NOT capturing coroutine lambdas.
    co_await nxtrt::when_all(std::tuple{
        [&session] { return capture(session); },
        [&session, deadline] { return monitor(session, deadline); },
    });
  } catch (...) {
    failure = std::current_exception();
  }
  if (!session.reaped && session.child.pid > 0) {
    session.exit = co_await nxtrt::shield(
        nxtrt::subprocess::terminate_and_wait(session.child));
    session.reaped = true;
  }
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
  app.live_run.clear();
  auto summary = co_await app.workers.run(
      [&app, run = session.run] { return app.data->summary(run); });
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

nxtrt::task<nxtrt::http::response> handle(Application &app,
                                          nxtrt::http::request req) {
  using nxtrt::http::response;
  if (req.method != "GET" && req.method != "HEAD")
    co_return response{405, {{"Allow", "GET, HEAD"}}, "Read-only viewer\n"};
  auto question = req.target.find('?');
  auto path = req.target.substr(0, question);
  if (path == "/htmx.js")
    co_return response{200, {{"Content-Type", "text/javascript"}}, app.htmx};
  if (path != "/" && path != "/state" && path != "/logs" &&
      path != "/api/state" && path != "/api/logs")
    co_return response{404, {}, "Not found\n"};
  std::map<std::string, std::string> params;
  std::uint64_t after = 0;
  try {
    if (question != std::string::npos) {
      auto query = std::string_view(req.target).substr(question + 1);
      while (!query.empty()) {
        auto end = query.find('&');
        auto item = query.substr(0, end);
        auto equal = item.find('=');
        if (equal != std::string_view::npos)
          params[decode(item.substr(0, equal))] =
              decode(item.substr(equal + 1));
        if (end == std::string_view::npos)
          break;
        query.remove_prefix(end + 1);
      }
    }
    if (params.contains("after")) {
      auto &v = params.at("after");
      auto result = std::from_chars(v.data(), v.data() + v.size(), after);
      if (result.ec != std::errc{} || result.ptr != v.data() + v.size())
        throw std::runtime_error("invalid cursor");
    }
  } catch (const std::exception &) {
    co_return response{400, {}, "Invalid query\n"};
  }
  auto run = params["run"], activity = params["activity"];
  bool is_logs = path == "/logs" || path == "/api/logs";
  auto result = co_await app.workers.run([&app, run, activity, after, is_logs] {
    return is_logs ? app.data->logs(run, activity, after)
                   : app.data->view(run, activity);
  });
  if (!is_logs && result.at("session").is_object()) {
    bool live = result["session"]["run"] == app.live_run &&
                !result["session"]["complete"].get<bool>();
    result["live"] = live;
    if (live)
      result["elapsed_now_ns"] = campaign::monotonic_ns() - app.live_start;
  }
  bool api = path.starts_with("/api/");
  auto body = api       ? result.dump()
              : is_logs ? campaign::web_logs(result, run, activity, after)
              : path == "/state" ? campaign::web_state(result, run, activity)
                                 : campaign::web_page(result, run, activity);
  co_return response{
      200,
      {{"Content-Type", api ? "application/json" : "text/html; charset=utf-8"},
       {"Cache-Control", "no-store"},
       {"X-Content-Type-Options", "nosniff"}},
      std::move(body)};
}

struct Options {
  std::string command, path, drv, store = "daemon", run, directory;
  std::uint16_t port = 8080;
  double speed = 1;
  unsigned budget = 7200, root_timeout = 900;
  bool raw = false;
};

nxtrt::task<int> server_body(nxtrt::firm &scope, Application &app,
                             const Options &options, int listener) {
  scope.fork([&app, listener] {
    nxtrt::http::server_options opts;
    opts.max_connections = 8;
    return nxtrt::http::serve(
        listener,
        [&app](nxtrt::http::request req) {
          return handle(app, std::move(req));
        },
        opts);
  });
  int code = 0;
  if (options.command == "watch")
    code = co_await record(app, options.drv, options.store);
  if (options.command == "cohort") {
    auto manifest = co_await app.workers.run([&app, path = options.drv] {
      // A service restart serves its existing recording; it never retries
      // builds.
      if (!app.data->view("", "").at("sessions").empty())
        return json(nullptr);
      std::ifstream file{path};
      auto value = json::parse(file);
      if (!value.at("id").is_string() ||
          value.at("id").get<std::string>().empty() ||
          !value.at("name").is_string() || !value.at("roots").is_array() ||
          value.at("roots").empty() || value.at("roots").size() > 256)
        throw std::runtime_error("invalid cohort manifest");
      for (const auto &root : value.at("roots")) {
        if (!root.at("name").is_string() || !root.at("drv").is_string() ||
            !root.at("drv").get<std::string>().ends_with(".drv"))
          throw std::runtime_error("invalid cohort root");
      }
      return value;
    });
    if (!manifest.is_null()) {
      auto end = campaign::monotonic_ns() +
                 std::int64_t(options.budget) * 1'000'000'000;
      bool recorder_error = false;
      for (std::size_t index = 0; index < manifest.at("roots").size();
           ++index) {
        if (requested_signal || campaign::monotonic_ns() >= end)
          break;
        const auto &root = manifest.at("roots")[index];
        json request = {{"name", root.at("name")},
                        {"cohort", manifest},
                        {"index", index},
                        {"budget_seconds", options.budget},
                        {"root_timeout_seconds", options.root_timeout}};
        auto deadline = std::min(end, campaign::monotonic_ns() +
                                          std::int64_t(options.root_timeout) *
                                              1'000'000'000);
        std::exception_ptr failure;
        try {
          auto result = co_await record(app, root.at("drv"), options.store,
                                        std::move(request), deadline);
          if (result)
            code = result;
        } catch (...) {
          failure = std::current_exception();
        }
        if (failure) {
          app.live_run.clear();
          recorder_error = true;
          code = 2;
          std::cerr << "Cohort recording stopped; serving committed "
                       "observations only\n";
          break;
        }
      }
      // Cohort admission ends after its last root settles. Keep this durable
      // even when the overall deadline falls between two roots.
      if (app.live_start && !recorder_error) {
        std::string reason = requested_signal ? "cancelled"
                             : campaign::monotonic_ns() >= end
                                 ? "budget-exhausted"
                                 : "all-roots-attempted";
        co_await nxtrt::shield(app.workers.run(
            [&app, reason,
             elapsed = campaign::monotonic_ns() - app.live_start] {
              auto last = app.data->summary();
              json event = {{"version", 1},
                            {"run", last.at("run")},
                            {"seq", last.at("events").get<std::uint64_t>() + 1},
                            {"wall_ns", campaign::wall_ns()},
                            {"elapsed_ns", elapsed},
                            {"kind", "cohort.finished"},
                            {"payload", {{"reason", reason}}}};
              app.data->append(json::array({std::move(event)}));
            }));
      }
      std::cerr << "Cohort admission finished; viewer remains available\n";
    } else {
      std::cerr << "Existing recording: serving only, no automatic retries\n";
    }
  }
  while (!requested_signal)
    co_await nxtrt::op::timeout::after(100ms);
  co_return code;
}

nxtrt::task<void> stop_server(nxtrt::firm &scope) {
  scope.stop();
  co_await scope.join();
}

nxtrt::task<int> execute(Application &app, const Options &options) {
  co_await app.workers.run([&app, path = options.path,
                            writable = options.command == "record" ||
                                       options.command == "watch" ||
                                       options.command == "cohort"] {
    app.data = std::make_unique<campaign::Dataset>(path, writable);
    auto assets = std::getenv("CAMPAIGN_STATIC_DIR");
    auto base = assets ? std::filesystem::path(assets)
                       : std::filesystem::read_symlink("/proc/self/exe")
                                 .parent_path()
                                 .parent_path() /
                             "share/filnix-campaign";
    std::ifstream file{base / "htmx.js", std::ios::binary};
    app.htmx.assign(std::istreambuf_iterator<char>{file}, {});
  });
  if (options.command == "record")
    co_return co_await record(app, options.drv, options.store);
  if (options.command == "watch" || options.command == "serve" ||
      options.command == "cohort") {
    if (app.htmx.empty())
      throw std::runtime_error("missing HTMX asset; set CAMPAIGN_STATIC_DIR");
    auto listener = nxtrt::net::listen_tcp_loopback(options.port);
    std::cerr << "Listening on http://127.0.0.1:"
              << ntohs(nxtrt::net::socket_address(listener.get()).sin_port)
              << std::endl;
    co_return co_await nxtrt::with_firm([&](nxtrt::firm &scope) {
      return nxtrt::finally(server_body(scope, app, options, listener.get()),
                            [&scope] { return stop_server(scope); });
    });
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
  co_await nxtrt::shield(app.workers.run([&app] { app.data.reset(); }));
  co_await app.workers.close();
}

} // namespace

int main(int argc, char **argv) {
  try {
    if (argc < 3)
      throw std::runtime_error(
          "usage: filnix-campaign record|watch DRV DATABASE "
          "[--store URI] [--port N]; cohort MANIFEST DATABASE "
          "[--store URI] [--port N] [--budget SECONDS] [--root-timeout "
          "SECONDS]; "
          "serve|inspect|replay DATABASE "
          "[--run ID] [--port N] [--speed N] [--json]; export DATABASE "
          "DIRECTORY");
    Options options;
    options.command = argv[1];
    int i = 2;
    if (options.command == "record" || options.command == "watch" ||
        options.command == "cohort") {
      if (argc < 4)
        throw std::runtime_error("build requires DRV and DATABASE");
      options.drv = argv[i++];
    } else if (options.command != "serve" && options.command != "inspect" &&
               options.command != "replay" && options.command != "export")
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
           options.command == "cohort"))
        options.store = value;
      else if (flag == "--run" &&
               (options.command == "inspect" || options.command == "replay"))
        options.run = value;
      else if (flag == "--port" &&
               (options.command == "serve" || options.command == "watch" ||
                options.command == "cohort")) {
        unsigned n;
        auto result =
            std::from_chars(value.data(), value.data() + value.size(), n);
        if (result.ec != std::errc{} ||
            result.ptr != value.data() + value.size() || n > 65535)
          throw std::runtime_error("invalid port");
        options.port = n;
      } else if ((flag == "--budget" || flag == "--root-timeout") &&
                 options.command == "cohort") {
        unsigned n;
        auto result =
            std::from_chars(value.data(), value.data() + value.size(), n);
        if (result.ec != std::errc{} ||
            result.ptr != value.data() + value.size() || !n || n > 86400)
          throw std::runtime_error("budget must be 1–86400 seconds");
        (flag == "--budget" ? options.budget : options.root_timeout) = n;
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

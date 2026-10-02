#include "journal.hh"

#include <nxtrt/app.hpp>
#include <nxtrt/subprocess.hpp>

#include <array>
#include <cmath>
#include <csignal>
#include <fcntl.h>
#include <filesystem>
#include <iomanip>
#include <spawn.h>
#include <sstream>
#include <sys/syscall.h>
#include <sys/wait.h>

extern char **environ;

using namespace std::chrono_literals;
using campaign::json;

namespace
{

volatile std::sig_atomic_t requested_signal = 0;
void request_stop(int signal) { requested_signal = signal; }

void display(const json &event, int fd)
{
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
                                const std::string &store)
{
    // Only fd 3 carries the event protocol. stdout/stderr remain ordinary
    // diagnostics, so a runtime diagnostic cannot corrupt the event pipe.
    int pipe[2];
    if (::pipe2(pipe, O_CLOEXEC) != 0)
        throw campaign::system_error("pipe");
    nxt::unique_fd reader{pipe[0]}, writer{pipe[1]};
    auto worker =
        std::filesystem::read_symlink("/proc/self/exe").parent_path() /
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
    return {.pid = pid,
            .pidfd = nxt::unique_fd{pidfd},
            .output = std::move(reader)};
}

struct Session {
    campaign::Journal &journal;
    nxtrt::piped_child child;
    bool done = false, reaped = false;
    nxtrt::child_result exit{};

    void append(std::string kind, json payload, bool commit = false)
    {
        display(journal.append(std::move(kind), std::move(payload), commit),
                STDERR_FILENO);
    }
};

nxtrt::task<void> capture(Session &session)
{
    std::exception_ptr failure;
    try {
        std::array<std::byte, 64 * 1024> buffer;
        std::string pending;
        while (auto count = co_await nxtrt::op::read_some{
                   session.child.output_fd(), buffer}) {
            pending.append(reinterpret_cast<const char *>(buffer.data()),
                           count);
            std::size_t consumed = 0;
            while (true) {
                auto end = pending.find('\n', consumed);
                if (end == std::string::npos)
                    break;
                if (end - consumed + 1 > campaign::max_record_bytes)
                    throw std::runtime_error("worker event exceeds 8 MiB");
                auto event = json::parse(pending.begin() + consumed,
                                         pending.begin() + end);
                auto payload = event.at("payload");
                payload["capture"] = {
                    {"wall_ns", event.at("captured_wall_ns")},
                    {"mono_ns", event.at("captured_mono_ns")},
                };
                session.append(event.at("kind"), std::move(payload));
                consumed = end + 1;
            }
            pending.erase(0, consumed);
            if (pending.size() > campaign::max_record_bytes)
                throw std::runtime_error("worker event exceeds 8 MiB");
        }
        if (!pending.empty())
            throw std::runtime_error(
                "worker event stream has a torn final record");
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

nxtrt::task<void> monitor(Session &session)
{
    unsigned ticks = 0;
    std::optional<std::chrono::steady_clock::time_point> stopping;
    while (!session.done) {
        if (requested_signal && !stopping) {
            session.append("run.cancel-requested",
                           {{"signal", requested_signal}}, true);
            co_await nxtrt::subprocess::signal_child(session.child, SIGINT);
            stopping = std::chrono::steady_clock::now();
        }
        if (stopping && std::chrono::steady_clock::now() - *stopping > 2s)
            co_await nxtrt::subprocess::signal_child(session.child, SIGKILL);
        if (++ticks % 10 == 0)
            session.journal.sync();
        co_await nxtrt::op::timeout::after(100ms);
    }
}

nxtrt::task<int> record(campaign::Journal &journal, std::string drv,
                        std::string store)
{
    journal.append("run.requested", {{"drv", drv}, {"store", store}}, true);
    Session session{journal, spawn_worker(drv, store)};
    std::exception_ptr failure;
    try {
        // These lambdas are factories, NOT capturing coroutine lambdas.
        co_await nxtrt::when_all(std::tuple{
            [&session] { return capture(session); },
            [&session] { return monitor(session); },
        });
    } catch (...) {
        failure = std::current_exception();
    }
    if (!session.reaped) {
        session.exit =
            co_await nxtrt::subprocess::terminate_and_wait(session.child);
        session.reaped = true;
    }
    if (failure) {
        std::string error;
        try {
            std::rethrow_exception(failure);
        } catch (const std::exception &e) {
            error = e.what();
        }
        journal.append("run.recorder-error",
                       {{"text_hex", campaign::hex(error)}});
    }
    session.append("run.finished",
                   {
                       {"exited", session.exit.exited},
                       {"exit_code", session.exit.exit_code},
                       {"signaled", session.exit.signaled},
                       {"signal", session.exit.signal},
                   },
                   true);
    std::cout << journal.projection().summary().dump() << '\n';
    if (failure)
        std::rethrow_exception(failure);
    co_return session.exit.exited ? session.exit.exit_code
                                  : 128 + session.exit.signal;
}

nxtrt::task<void> replay(std::string path, double speed, bool raw)
{
    campaign::JournalReader reader{path};
    json event;
    auto start = std::chrono::steady_clock::now();
    std::optional<std::int64_t> first;
    while (reader.next(event)) {
        auto elapsed = event.at("elapsed_ns").get<std::int64_t>();
        if (!first)
            first = elapsed;
        if (speed > 0) {
            double seconds =
                static_cast<double>(elapsed - *first) / 1e9 / speed;
            if (!std::isfinite(seconds) || seconds > 1e9)
                throw std::runtime_error("replay delay is too large");
            auto target =
                start + std::chrono::duration_cast<std::chrono::nanoseconds>(
                            std::chrono::duration<double>{seconds});
            if (auto delay = target - std::chrono::steady_clock::now();
                delay > 0ns)
                co_await nxtrt::op::timeout::after(delay);
        }
        if (raw)
            campaign::write_all(STDOUT_FILENO, event.dump() + "\n");
        else
            display(event, STDOUT_FILENO);
    }
    if (reader.torn_tail_bytes())
        std::cerr << "Ignored " << reader.torn_tail_bytes()
                  << " torn tail bytes\n";
}

} // namespace

int main(int argc, char **argv)
{
    try {
        if (argc >= 4 && std::string_view(argv[1]) == "record") {
            std::string store = "daemon";
            if (argc == 6 && std::string_view(argv[4]) == "--store")
                store = argv[5];
            else if (argc != 4)
                throw std::runtime_error("record: unexpected arguments");
            std::signal(SIGINT, request_stop);
            std::signal(SIGTERM, request_stop);
            campaign::Journal journal{argv[3]};
            nxtrt::runtime runtime;
            return runtime.run([&] { return record(journal, argv[2], store); });
        }
        if (argc >= 3 && std::string_view(argv[1]) == "replay") {
            double speed = 1;
            bool raw = false;
            for (int i = 3; i < argc; ++i) {
                if (std::string_view(argv[i]) == "--json")
                    raw = true;
                else if (std::string_view(argv[i]) == "--speed" &&
                         i + 1 < argc) {
                    std::size_t consumed;
                    std::string value = argv[++i];
                    speed = std::stod(value, &consumed);
                    if (consumed != value.size() || !std::isfinite(speed) ||
                        speed < 0)
                        throw std::runtime_error(
                            "speed must be finite and nonnegative (0 means "
                            "unpaced)");
                } else
                    throw std::runtime_error("replay: unexpected arguments");
            }
            nxtrt::runtime runtime;
            runtime.run([&] { return replay(argv[2], speed, raw); });
            return 0;
        }
        if (argc == 3 && std::string_view(argv[1]) == "inspect") {
            campaign::JournalReader reader{argv[2]};
            campaign::Projection projection;
            json event;
            while (reader.next(event))
                projection.apply(event);
            auto summary = projection.summary();
            summary["torn_tail_bytes"] = reader.torn_tail_bytes();
            std::cout << summary.dump() << '\n';
            return 0;
        }
        std::cerr
            << "Usage:\n"
               "  filnix-campaign record DRV JOURNAL [--store URI]\n"
               "  filnix-campaign replay JOURNAL [--speed NUMBER] [--json]\n"
               "  filnix-campaign inspect JOURNAL\n";
        return 2;
    } catch (const std::exception &error) {
        std::cerr << "filnix-campaign: " << error.what() << '\n';
        return 2;
    }
}

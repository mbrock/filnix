#include "journal.hh"

#include <array>
#include <fcntl.h>
#include <filesystem>
#include <sys/random.h>

namespace campaign
{

Journal::Journal(const std::string &path)
{
    std::array<char, 16> random;
    if (::getrandom(random.data(), random.size(), 0) !=
        static_cast<ssize_t>(random.size()))
        throw system_error("getrandom");
    run_ = hex({random.data(), random.size()});
    fd_ = ::open(path.c_str(), O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0640);
    if (fd_ < 0)
        throw system_error(
            "create journal (existing journals are never overwritten)");
    auto parent = std::filesystem::path(path).parent_path();
    if (parent.empty())
        parent = ".";
    int directory = ::open(parent.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    int result = directory < 0 ? -1 : ::fsync(directory);
    if (directory >= 0)
        ::close(directory);
    if (result < 0) {
        ::close(fd_);
        throw system_error("sync journal directory");
    }
}

Journal::~Journal() { ::close(fd_); }

json Journal::append(std::string kind, json payload, bool commit)
{
    json event = {
        {"version", 1},
        {"run", run_},
        {"seq", seq_ + 1},
        {"wall_ns", wall_ns()},
        {"elapsed_ns", monotonic_ns() - start_},
        {"kind", std::move(kind)},
        {"payload", std::move(payload)},
    };
    auto record = event.dump() + "\n";
    if (record.size() > max_record_bytes)
        throw std::runtime_error("journal record exceeds 8 MiB");
    write_all(fd_, record);
    ++seq_;
    dirty_ += record.size();
    if (commit || dirty_ >= 64 * 1024)
        sync();
    projection_.apply(event);
    return event;
}

void Journal::sync()
{
    if (dirty_ && ::fdatasync(fd_) != 0)
        throw system_error("sync journal");
    dirty_ = 0;
}

void Projection::apply(const json &event)
{
    ++events_;
    run_ = event.at("run");
    const auto &kind = event.at("kind");
    const auto &payload = event.at("payload");
    if (kind == "run.requested")
        root_ = payload.at("drv");
    else if (kind == "nix.activity-started")
        ++activities_;
    else if (kind == "nix.result" && payload.value("build_output", false))
        ++output_lines_;
    else if (kind == "run.cancel-requested")
        cancelled_ = true;
    else if (kind == "run.recorder-error")
        recorder_error_ = true;
    else if (kind == "worker.error")
        worker_error_ = true;
    else if (kind == "nix.build-result") {
        has_result_ = true;
        result_success_ = payload.at("success");
        result_outcome_ = payload.at("outcome");
        outputs_ = payload.at("outputs");
    } else if (kind == "run.finished") {
        complete_ = true;
        exited_ = payload.at("exited");
        exit_code_ = payload.at("exit_code");
    }
}

json Projection::summary() const
{
    std::string outcome = "incomplete";
    if (complete_) {
        if (recorder_error_)
            outcome = "recorder-error";
        else if (has_result_ && result_success_ && exited_ && exit_code_ == 0)
            outcome = result_outcome_;
        else if (cancelled_)
            outcome = "cancelled";
        else if (has_result_ && !result_success_)
            outcome = "failed";
        else if (worker_error_)
            outcome = "worker-error";
        else
            outcome = "interrupted";
    }
    return {
        {"run", run_},
        {"drv", root_},
        {"events", events_},
        {"activities", activities_},
        {"output_lines", output_lines_},
        {"complete", complete_},
        {"outcome", outcome},
        {"outputs", outputs_},
    };
}

JournalReader::JournalReader(const std::string &path)
    : input_(path, std::ios::binary)
{
    if (!input_)
        throw std::runtime_error("cannot open journal: " + path);
}

bool JournalReader::next(json &event)
{
    input_.getline(buffer_.data(), buffer_.size());
    auto count = input_.gcount();
    if (input_.bad())
        throw std::runtime_error("journal read failed");
    if (input_.eof()) {
        torn_tail_ = count;
        if (!seq_)
            throw std::runtime_error("journal has no complete records");
        return false;
    }
    if (input_.fail() || count > static_cast<std::streamsize>(max_record_bytes))
        throw std::runtime_error("journal record exceeds 8 MiB");
    event = json::parse(buffer_.data(), buffer_.data() + count - 1);
    if (terminal_ || event.at("version") != 1 ||
        !event.at("seq").is_number_unsigned() ||
        event.at("seq").get<std::uint64_t>() != seq_ + 1 ||
        !event.at("elapsed_ns").is_number_integer() ||
        event.at("elapsed_ns").get<std::int64_t>() < elapsed_ ||
        !event.at("wall_ns").is_number_integer() ||
        !event.at("kind").is_string() || !event.at("payload").is_object())
        throw std::runtime_error("invalid journal envelope or ordering");
    auto run = event.at("run").get<std::string>();
    if (!seq_) {
        if (run.empty() || event.at("kind") != "run.requested")
            throw std::runtime_error("journal must start with run.requested");
        run_ = run;
    } else if (run != run_)
        throw std::runtime_error("journal mixes run identities");
    ++seq_;
    elapsed_ = event.at("elapsed_ns");
    terminal_ = event.at("kind") == "run.finished";
    return true;
}

} // namespace campaign

#pragma once

#include <nlohmann/json.hpp>

#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unistd.h>
#include <vector>

namespace campaign
{

using json = nlohmann::json;
inline constexpr std::size_t max_record_bytes = 8 * 1024 * 1024;

inline std::runtime_error system_error(std::string_view operation)
{
    return std::runtime_error(std::string(operation) + ": " +
                              std::strerror(errno));
}

inline void write_all(int fd, std::string_view bytes)
{
    while (!bytes.empty()) {
        auto written = ::write(fd, bytes.data(), bytes.size());
        if (written < 0 && errno == EINTR)
            continue;
        if (written <= 0)
            throw system_error("write");
        bytes.remove_prefix(written);
    }
}

inline std::int64_t wall_ns()
{
    return std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::system_clock::now().time_since_epoch())
        .count();
}

inline std::int64_t monotonic_ns()
{
    return std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::steady_clock::now().time_since_epoch())
        .count();
}

// Logger strings may contain arbitrary builder bytes, not necessarily UTF-8.
inline std::string hex(std::string_view bytes)
{
    constexpr char digits[] = "0123456789abcdef";
    std::string result;
    result.reserve(bytes.size() * 2);
    for (unsigned char byte : bytes) {
        result += digits[byte >> 4];
        result += digits[byte & 15];
    }
    return result;
}

inline std::string unhex(std::string_view bytes)
{
    auto digit = [](char c) -> unsigned {
        if (c >= '0' && c <= '9')
            return c - '0';
        if (c >= 'a' && c <= 'f')
            return c - 'a' + 10;
        throw std::runtime_error("invalid hex-encoded bytes");
    };
    if (bytes.size() % 2)
        throw std::runtime_error("odd hex-encoded byte count");
    std::string result;
    result.reserve(bytes.size() / 2);
    for (std::size_t i = 0; i < bytes.size(); i += 2)
        result +=
            static_cast<char>((digit(bytes[i]) << 4) | digit(bytes[i + 1]));
    return result;
}

class Projection
{
  public:
    void apply(const json &event);
    json summary() const;

  private:
    std::string run_, root_, result_outcome_;
    json outputs_ = json::array();
    std::uint64_t events_ = 0, activities_ = 0, output_lines_ = 0;
    bool complete_ = false, cancelled_ = false, recorder_error_ = false;
    bool result_success_ = false, has_result_ = false, worker_error_ = false;
    bool exited_ = false;
    int exit_code_ = -1;
};

class Journal
{
  public:
    explicit Journal(const std::string &path);
    ~Journal();
    Journal(const Journal &) = delete;
    Journal &operator=(const Journal &) = delete;

    json append(std::string kind, json payload, bool commit = false);
    void sync();
    const Projection &projection() const { return projection_; }

  private:
    int fd_ = -1;
    std::string run_;
    std::uint64_t seq_ = 0;
    std::int64_t start_ = monotonic_ns();
    std::size_t dirty_ = 0;
    Projection projection_;
};

// Only complete newline-terminated records are observations. A torn tail is
// reported separately; corruption of a complete record is never ignored.
class JournalReader
{
  public:
    explicit JournalReader(const std::string &path);
    bool next(json &event);
    std::size_t torn_tail_bytes() const { return torn_tail_; }

  private:
    std::ifstream input_;
    std::vector<char> buffer_ = std::vector<char>(max_record_bytes + 2);
    std::string run_;
    std::uint64_t seq_ = 0;
    std::int64_t elapsed_ = 0;
    std::size_t torn_tail_ = 0;
    bool terminal_ = false;
};

} // namespace campaign

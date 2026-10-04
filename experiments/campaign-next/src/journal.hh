#pragma once

#include <nlohmann/json.hpp>

#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unistd.h>

namespace campaign {

using json = nlohmann::json;
inline constexpr std::size_t max_record_bytes = 8 * 1024 * 1024;
// Console windows: the initial tail, and each "earlier output" page.
inline constexpr std::size_t log_tail_rows = 500, log_earlier_rows = 1000;

inline std::runtime_error system_error(std::string_view operation) {
  return std::runtime_error(std::string(operation) + ": " +
                            std::strerror(errno));
}

inline void write_all(int fd, std::string_view bytes) {
  while (!bytes.empty()) {
    auto written = ::write(fd, bytes.data(), bytes.size());
    if (written < 0 && errno == EINTR)
      continue;
    if (written <= 0)
      throw system_error("write");
    bytes.remove_prefix(written);
  }
}

inline std::int64_t wall_ns() {
  return std::chrono::duration_cast<std::chrono::nanoseconds>(
             std::chrono::system_clock::now().time_since_epoch())
      .count();
}

inline std::int64_t monotonic_ns() {
  return std::chrono::duration_cast<std::chrono::nanoseconds>(
             std::chrono::steady_clock::now().time_since_epoch())
      .count();
}

// Logger strings may contain arbitrary builder bytes, not necessarily UTF-8.
inline std::string hex(std::string_view bytes) {
  constexpr char digits[] = "0123456789abcdef";
  std::string result;
  result.reserve(bytes.size() * 2);
  for (unsigned char byte : bytes) {
    result += digits[byte >> 4];
    result += digits[byte & 15];
  }
  return result;
}

inline std::string unhex(std::string_view bytes) {
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
    result += static_cast<char>((digit(bytes[i]) << 4) | digit(bytes[i + 1]));
  return result;
}

class Projection {
public:
  void apply(const json &event);
  json summary() const;

private:
  std::string run_, root_, result_outcome_;
  json outputs_ = json::array();
  std::uint64_t events_ = 0, activities_ = 0, output_lines_ = 0;
  bool complete_ = false, cancelled_ = false, recorder_error_ = false;
  bool timed_out_ = false;
  bool result_success_ = false, has_result_ = false, worker_error_ = false;
  bool exited_ = false;
  int exit_code_ = -1;
};

} // namespace campaign

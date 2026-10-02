#include "dataset.hh"
#include "web.hh"

#include <iostream>

using campaign::json;

void check(bool condition, const char *message) {
  if (!condition)
    throw std::runtime_error(message);
}

int main() {
  try {
    campaign::Dataset data{":memory:", true};
    auto event = [](unsigned seq, std::string kind, json payload) {
      return json{
          {"version", 1},          {"run", "test'run"},       {"seq", seq},
          {"wall_ns", 1000 + seq}, {"elapsed_ns", 100 * seq}, {"kind", kind},
          {"payload", payload}};
    };
    data.append(json::array({event(
        1, "run.requested", {{"drv", "/store/a'b.drv"}, {"store", "test"}})}));
    const auto activity = UINT64_MAX - 6;
    json start = {{"id", activity},
                  {"parent", 0},
                  {"type", 105},
                  {"text_hex", ""},
                  {"drv", "/store/a'b.drv"},
                  {"machine", "ssh://builder"}};
    const std::string bytes{"a\0b\xff<script>", 12};
    json line = {
        {"id", activity},
        {"type", 101},
        {"build_output", true},
        {"fields", json::array({{{"string_hex", campaign::hex(bytes)}}})}};
    bool failed = false;
    try {
      data.append(json::array({event(2, "nix.activity-started", start),
                               event(3, "nix.result", line),
                               event(4, "nix.activity-started", start)}));
    } catch (const std::exception &) {
      failed = true;
    }
    check(failed, "duplicate activity must fail the batch");
    auto view = data.view("test'run", "");
    check(view.at("watermark") == 1 && view.at("session").at("events") == 1,
          "rollback must not publish the offset or summary");
    check(view.at("activities").empty() && view.at("logs").empty() &&
              data.events("test'run", 1).empty(),
          "rollback must cover every table");
    data.append(json::array(
        {event(2, "nix.activity-started", start),
         event(3, "nix.result",
               {{"id", activity},
                {"type", 104},
                {"fields", json::array({{{"string_hex",
                                          campaign::hex("buildPhase")}}})}}),
         event(4, "nix.result", line),
         event(5, "nix.activity-stopped", {{"id", activity}}),
         event(6, "nix.future-record", {{"unknown", "kept verbatim"}})}));
    view = data.view("test'run", "");
    check(view.at("watermark") == 6, "rollback must not consume offsets");
    check(view.at("session").at("outcome") == "incomplete",
          "activity stop must not mean success");
    check(view.at("activities")[0].at("id") == std::to_string(activity),
          "activity IDs must remain exact beyond signed and JS integer ranges");
    check(view.at("activities")[0].at("phase") == "buildPhase",
          "phase projection");
    auto logs = data.logs("test'run", std::to_string(activity), 3);
    check(logs.size() == 1 &&
              campaign::unhex(logs[0].at("bytes_hex").get<std::string>()) ==
                  bytes,
          "binary output must survive projection");
    check(data.logs("test'run", "different", 0).empty() &&
              data.logs("test'run", std::to_string(activity), 4).empty(),
          "exclusive filtered cursor");
    auto events = data.events("test'run", 5);
    check(events.size() == 1 &&
              events[0].at("payload").at("unknown") == "kept verbatim",
          "unknown observations must survive");
    auto fragment =
        campaign::web_logs(logs, "test'run", std::to_string(activity), 3);
    check(
        fragment.starts_with(
            "<div hx-swap-oob=\"beforeend:#log-rows\"><div class=\"log-row\""),
        "HTMX must append rows inside a disposable OOB wrapper");
    check(fragment.find("&lt;script&gt;") != std::string::npos &&
              fragment.find("<script>") == std::string::npos,
          "escape captured HTML");
    std::cout << "transaction rollback, binary output, cursor, unknown events "
                 "and HTMX structure passed\n";
  } catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
  }
}

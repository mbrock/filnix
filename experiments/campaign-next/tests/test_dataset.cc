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
    check(view.at("phases").size() == 1 &&
              view.at("phases")[0].at("activity") == std::to_string(activity) &&
              view.at("phases")[0].at("seq") == 3,
          "phase jump retains exact activity and event cursor");
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
    data.append(json::array(
        {event(7, "nix.result",
               {{"id", activity}, {"type", 104}, {"fields", json::array()}})}));
    check(data.view("test'run", "").at("phases").size() == 1 &&
              data.events("test'run", 6)[0].at("payload").at("fields").empty(),
          "unsupported phase fields stay raw, not selectable phases");
    auto fragment =
        campaign::web_logs(logs, "test'run", std::to_string(activity), 3);
    check(
        fragment.starts_with(
            "<div hx-swap-oob=\"beforeend:#log-rows\"><div class=\"log-row\""),
        "HTMX must append rows inside a disposable OOB wrapper");
    check(fragment.find("&lt;script&gt;") != std::string::npos &&
              fragment.find("<script>") == std::string::npos,
          "escape captured HTML");
    check(fragment.find("#" + std::to_string(activity)) != std::string::npos,
          "full unsigned activity id is visible and copyable");
    auto large = view;
    large["recipes"] = json::array();
    large["edges"] = json::array();
    large["recipes"].push_back(
        {{"drv", "/store/a'b.drv"}, {"name", "root-gnufilc0-9.7"}});
    auto add = [&](std::string parent, std::string drv, std::string name,
                   json outputs) {
      large["recipes"].push_back({{"drv", drv}, {"name", name}});
      large["edges"].push_back({{"parent_drv", parent},
                                {"child_drv", drv},
                                {"outputs", outputs},
                                {"dynamic", false}});
    };
    add("/store/a'b.drv", "/lib.drv", "lib-gnufilc0-4.2",
        json::array({"out", "dev"}));
    add("/store/a'b.drv", "/z.drv", "z-gnufilc0-9.8", json::array({"dev"}));
    large["edges"].push_back({{"parent_drv", "/lib.drv"},
                              {"child_drv", "/z.drv"},
                              {"outputs", json::array({"out"})},
                              {"dynamic", false}});
    std::string parent = "/lib.drv";
    for (unsigned i = 0; i < 501; ++i) {
      auto drv = "/bash" + std::to_string(i) + ".drv";
      add(parent, drv, "bash-" + std::to_string(i), json::array({"out"}));
      parent = drv;
    }
    auto page = campaign::web_page(large, "test'run", "");
    check(page.find("501 static inputs") != std::string::npos &&
              page.find("bash-0</a>") == std::string::npos &&
              page.find("lib-gnufilc0-4.2</a>") != std::string::npos,
          "default graph renders signal, not collapsed DOM");
    check(page.find("outputs · out, dev") != std::string::npos &&
              page.find("outputs · out</span>") == std::string::npos,
          "only nondefault output sets are shown");
    check(
        page.find("z-gnufilc0-9.8</a><span>outputs · dev</span>") !=
            std::string::npos,
        "foreground uses root's edge outputs, not an earlier transitive edge");
    auto window = campaign::web_graph(large, "test'run", 0, "");
    auto marker = "Remaining dependencies omitted (500-node limit).";
    auto pos = window.find(marker);
    check(pos != std::string::npos &&
              window.find(marker, pos + 1) == std::string::npos,
          "one truncation notice per window");
    check(window.find("bash-499</a>") == std::string::npos &&
              window.find("Show next 500") != std::string::npos,
          "first graph window ends at its exact row boundary");
    auto next = campaign::web_graph(large, "test'run", 500, "");
    check(next.find("bash-499</a>") != std::string::npos &&
              next.find("bash-500</a>") != std::string::npos &&
              next.find("bash-498</a>") == std::string::npos,
          "next graph window replaces, not repeats, the first");
    check(campaign::web_graph(large, "test'run", 0, "/bash500.drv") == next,
          "deep links request the window containing the canonical node");
    for (auto outcome :
         {"failed", "timed-out", "interrupted", "cancelled", "worker-error"}) {
      auto failed_view = view;
      failed_view["session"]["complete"] = true;
      failed_view["session"]["outcome"] = outcome;
      failed_view["sessions"][0] = failed_view["session"];
      failed_view["failure_events"] = json::array(
          {{{"kind", "worker.error"},
            {"payload",
             {{"text_hex",
               campaign::hex("\x1b[31;1mfailure <detail>\x1b[0m")}}}}});
      auto html = campaign::web_page(failed_view, "test'run", "");
      check(html.find("class=\"failure\"") != std::string::npos &&
                html.find("failure &lt;detail&gt;") != std::string::npos,
            "failure modes have an escaped pinned reason");
      check(html.find("[31;1m") == std::string::npos,
            "strip reason SGR before sanitizing control bytes");
    }
    auto rail = view;
    rail["live_run"] = "elsewhere";
    rail["sessions"].push_back({{"run", "elsewhere"},
                                {"name", "running-gnufilc0-8.1"},
                                {"complete", false},
                                {"outcome", "incomplete"}});
    auto observing =
        campaign::web_sessions(rail, "test'run", "observing", "", 0);
    check(observing.find("running-gnufilc0-8.1") != std::string::npos &&
              observing.find("test%27run") == std::string::npos,
          "observing rail uses global live identity, not selected session");
    check(campaign::web_sessions(rail, "test'run", "observing", "elsewhere", 0)
                  .find("No sessions") != std::string::npos,
          "Find matches names, not opaque ids");
    std::cout << "transaction rollback, binary output, cursor, unknown events "
                 "and HTMX structure passed\n";
  } catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
  }
}

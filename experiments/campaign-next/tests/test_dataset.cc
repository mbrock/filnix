#include "dataset.hh"
#include "html.hh"
#include "web.hh"

#include <iostream>

using campaign::json;

void check(bool condition, const char *message) {
  if (!condition)
    throw std::runtime_error(message);
}

int main() {
  try {
    campaign::html::Writer document;
    document.tag("p", {{"data-name", "a\"<&"}}, [&] {
      document.text("start<");
      document.tag("span", [&] { document.text("child>"); });
      document.text("end&");
    });
    check(std::move(document).str() == "<p "
                                       "data-name=\"a&quot;&lt;&amp;\">start&"
                                       "lt;<span>child&gt;</span>end&amp;</p>",
          "block HTML construction preserves siblings and escapes "
          "text/attributes");
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
    check(fragment.find("data-source=\"") != std::string::npos &&
              fragment.find("<time title=\"") != std::string::npos &&
              fragment.find("#" + std::to_string(activity)) ==
                  std::string::npos,
          "rows carry a source label and clock time, not opaque activity ids");
    {
      json many = json::array();
      for (unsigned i = 0; i < campaign::log_earlier_rows; ++i)
        many.push_back(
            {{"seq", 2000 + i}, {"elapsed_ns", 0}, {"bytes_hex", ""}});
      auto page = campaign::web_logs(many, "test'run", "", 0, 3000);
      check(page.find("data-first=\"2000\">") != std::string::npos &&
                page.find("hx-swap-oob") == std::string::npos,
            "a full earlier page offers the next one before its first row");
      many.erase(many.begin());
      check(campaign::web_logs(many, "test'run", "", 0, 3000)
                    .find("data-first=\"2001\" hidden") != std::string::npos,
            "a short earlier page reaches the beginning");
    }
    unsigned seq = 8;
    for (const auto &[raw, rendered] :
         std::vector<std::pair<std::string, std::string>>{
             {"\x1b[31;1merror:\x1b[0m Cannot build "
              "'\x1b[35;1m<drv>&\x1b[0m'.\n"
              "       Reason: \x1b[31;1m1 dependency failed\x1b[0m.\n"
              "       Output paths:\n         \x1b[35;1m/store/result\x1b[0m",
              "<span "
              "style=\"color:var(--ansi-1);font-weight:700;\">error:</span> "
              "Cannot build &#39;"
              "<span "
              "style=\"color:var(--ansi-5);font-weight:700;\">&lt;drv&gt;&amp;<"
              "/span>&#39;.\n"
              "       Reason: <span "
              "style=\"color:var(--ansi-1);font-weight:700;\">1 dependency "
              "failed</span>.\n"
              "       Output paths:\n         <span "
              "style=\"color:var(--ansi-5);font-weight:700;\">/store/result</"
              "span>"},
             {"\x1b[38;2;10;20;30mRGB\x1b[39m + "
              "\x1b[38:2::80:90:100mcolon\x1b[m\tcafé",
              "<span style=\"color:rgb(10,20,30);\">RGB</span> + "
              "<span style=\"color:rgb(80,90,100);\">colon</span>\tcafé"},
             {"\x1b[1;38;5;196;48:5:232mindexed\x1b[22;39m bg\x1b[49m plain "
              "\x1b[3;4;9mstyled\x1b[23;24;29m normal",
              "<span "
              "style=\"color:rgb(255,0,0);background-color:rgb(8,8,8);font-"
              "weight:700;\">indexed</span>"
              "<span style=\"background-color:rgb(8,8,8);\"> bg</span> plain "
              "<span style=\"font-style:italic;text-decoration:underline "
              "line-through;\">styled</span> normal"},
             {"\x1b[91;104mbright\x1b[0m \x1b[7mreverse\x1b[27m default",
              "<span "
              "style=\"color:var(--ansi-9);background-color:var(--ansi-12);\">"
              "bright</span> "
              "<span "
              "style=\"color:var(--paper);background-color:var(--ink);\">"
              "reverse</span> default"},
             {"bad \x1b[38;2;256;0;0mRGB; \x1b[999mSGR; \x1b[31;999mcompound",
              "bad �[38;2;256;0;0mRGB; �[999mSGR; �[31;999mcompound"},
             {"literal [31;1m; \x1b[2J; \x1b[?31m; unfinished \x1b[31;",
              "literal [31;1m; �[2J; �[?31m; unfinished �[31;"}}) {
      auto decorated = line;
      decorated["fields"][0]["string_hex"] = campaign::hex(raw);
      data.append(json::array({event(seq, "nix.result", decorated)}));
      auto colored_logs =
          data.logs("test'run", std::to_string(activity), seq - 1);
      check(colored_logs.size() == 1 &&
                campaign::unhex(
                    colored_logs[0]["bytes_hex"].get<std::string>()) == raw &&
                data.events("test'run", seq - 1)[0]["payload"] == decorated,
            "terminal decoration stays byte-exact in logs and events");
      auto expected = "<pre>" + rendered + "</pre>";
      check(campaign::web_logs(colored_logs, "test'run",
                               std::to_string(activity), seq - 1)
                    .find(expected) != std::string::npos,
            "render SGR styles, resets and colors without interpreting HTML or "
            "unknown controls");
      check(campaign::web_page(data.view("test'run", ""), "test'run", "")
                    .find(expected) != std::string::npos,
            "initial output and streamed output use the same SGR rendering");
      ++seq;
    }
    data.append(json::array(
        {event(
             seq++, "nix.message",
             {{"level", 0}, {"text_hex", campaign::hex("dependency <error>")}}),
         event(seq++, "nix.message",
               {{"level", 1}, {"text_hex", campaign::hex("warning only")}}),
         event(
             seq++, "nix.build-result",
             {{"success", false},
              {"outcome", "failed"},
              {"outputs", json::array()},
              {"result",
               {{"status", "DependencyFailed"},
                {"errorMsg", "Cannot build /root.drv. Reason: 1 dependency "
                             "failed.\nOutput paths:\n/store/not-realized"}}}}),
         event(seq++, "run.finished", {{"exited", true}, {"exit_code", 1}})}));
    auto failure_view = data.view("test'run", "");
    check(
        failure_view["reported_errors"].size() == 1 &&
            campaign::unhex(failure_view["reported_errors"][0]["bytes_hex"]
                                .get<std::string>()) == "dependency <error>" &&
            failure_view["session"]["native_status"] == "DependencyFailed" &&
            failure_view["session"]["phase_hex"] == campaign::hex("buildPhase"),
        "index summaries and error reports use typed observations, not parsed "
        "log guesses");
    auto failure_page = campaign::web_page(failure_view, "test'run", "");
    check(failure_page.find("Output paths · reported") != std::string::npos &&
              failure_page.find("dependency &lt;error&gt;") !=
                  std::string::npos &&
              failure_view["session"]["outputs"].empty(),
          "reported paths/errors are not claimed to be realized outputs or a "
          "proven culprit");
    check(failure_view["session"]["cause_hex"] ==
                  campaign::hex("dependency <error>") &&
              failure_view["session"]["duration_ns"].is_number(),
          "roots carry their first top-level error and elapsed time");

    auto chained = failure_view;
    chained["session"]["name"] =
        "ffmpeg-headless-x86_64-unknown-linux-gnufilc0-8.1.2";
    chained["sessions"] = json::array({chained["session"]});
    chained["reported_errors"] = json::array(
        {{{"seq", 9},
          {"elapsed_ns", 2},
          {"bytes_hex",
           campaign::hex("\x1b[31;1merror:\x1b[0m Cannot build "
                         "'/nix/store/b-libopenmpt-x86_64-unknown-linux-"
                         "gnufilc0-0.8.9.drv'.\n       Reason: 1 dependency "
                         "failed.\n       Output paths:\n  /nix/store/c")}},
         {{"seq", 7},
          {"elapsed_ns", 1},
          {"bytes_hex",
           campaign::hex("error: building of '/nix/store/a-flac-x86_64-"
                         "unknown-linux-gnufilc0-1.5.0.drv' timed out after "
                         "300 seconds of silence")}}});
    auto chain = campaign::web_page(chained, "test'run", "");
    auto origin = chain.find("<li class=\"cause origin\"");
    auto middle = chain.find("libopenmpt</span><span class=\"version\">0.8.9");
    auto last = chain.find("ffmpeg-headless</span><span class=\"version\">"
                           "8.1.2</span><span class=\"cause-what\">1 "
                           "dependency failed");
    check(origin != std::string::npos &&
              chain.find("timed out after 300 seconds of silence") > origin &&
              middle > origin && middle != std::string::npos && last > middle &&
              last != std::string::npos &&
              chain.find("data-phase-seq=\"7\"") != std::string::npos,
          "failure card orders the chain from origin to the selected root");
    auto row = campaign::web_sessions(chained, "", "all", "", 0);
    check(row.find(">ffmpeg-headless</a>") != std::string::npos &&
              row.find("<td class=\"version\">8.1.2</td>") !=
                  std::string::npos &&
              row.find("unknown-linux-gnufilc0</a>") == std::string::npos,
          "rows name the package and version, not the platform triple");

    auto ledger = view;
    ledger["activities"][0]["stop_elapsed_ns"] = INT64_C(425125000000);
    ledger["activities"].push_back({{"id", "42"}, {"drv", "/dependency.drv"}});
    auto phase = [&](unsigned seq, const char *id, const char *name,
                     std::int64_t ns) {
      return json{
          {"seq", seq}, {"activity", id}, {"phase", name}, {"elapsed_ns", ns}};
    };
    auto id = std::to_string(activity);
    ledger["phases"] = json::array(
        {phase(21, id.c_str(), "unpackPhase", INT64_C(404475000000)),
         phase(22, "42", "otherPhase", INT64_C(404500000000)),
         phase(23, id.c_str(), "unpackPhase", INT64_C(404600000000)),
         phase(24, id.c_str(), "patchPhase", INT64_C(404942000000)),
         phase(25, id.c_str(), "buildPhase", INT64_C(410000000000))});
    auto measured = campaign::web_state(ledger, "test'run", "");
    auto unpack = measured.find("unpackPhase</button>");
    check(unpack != std::string::npos &&
              measured.find("unpackPhase</button>", unpack + 1) ==
                  std::string::npos &&
              measured.find("otherPhase") == std::string::npos &&
              measured.find("unpackPhase</button></td><td>0.5s") !=
                  std::string::npos &&
              measured.find("patchPhase</button></td><td>5.1s") !=
                  std::string::npos &&
              measured.find("buildPhase</button></td><td>15s") !=
                  std::string::npos,
          "phase duration ignores interleaved activities and duplicate phase "
          "reports, ending at activity stop");
    ledger["activities"][0]["stop_elapsed_ns"] = nullptr;
    ledger["activities"][0]["status"] = "running";
    ledger["elapsed_now_ns"] = INT64_C(430250000000);
    check(campaign::web_state(ledger, "test'run", "")
                  .find("— · end unobserved") != std::string::npos,
          "an abandoned activity has no invented terminal phase duration");
    ledger["live"] = true;
    check(campaign::web_state(ledger, "test'run", "").find("20s · running") !=
              std::string::npos,
          "a live phase uses elapsed observer time and is explicitly running");
    auto light = data.view("test'run", "", false);
    check(light["sessions"] == data.view("test'run", "")["sessions"] &&
              light["logs"].empty() && light["phases"].empty() &&
              light["activities"].empty(),
          "overview materializes summaries, not session details");
    auto overview = campaign::web_page(light, "", "");
    check(overview.find("campaign-table") != std::string::npos &&
              overview.find("graph-panel") == std::string::npos &&
              overview.find("log-panel") == std::string::npos &&
              overview.find("every ") == std::string::npos,
          "front page is an idle overview, not an implicit session");
    check(campaign::web_page(data.view("test'run", ""), "", "", true)
                  .find("graph-panel") != std::string::npos,
          "following latest is an explicit opt-in");
    check(failure_page.find("session-results") == std::string::npos &&
              failure_page.find("campaign-line") == std::string::npos &&
              failure_page.find("log-phase") == std::string::npos,
          "details contain one inspector/console, not a duplicate campaign "
          "list or phase dropdown");
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
    check(
        page.find("501 static inputs") != std::string::npos &&
            page.find("data-name=\"bash-0\"") == std::string::npos &&
            page.find(
                "lib-gnufilc0</span><span class=\"version\">4.2</span></a>") !=
                std::string::npos,
        "default graph renders signal, not collapsed DOM");
    check(page.find("outputs · out, dev") != std::string::npos &&
              page.find("outputs · out</span>") == std::string::npos,
          "only nondefault output sets are shown");
    check(
        page.find("9.8</span></a><span>outputs · dev</span>") !=
            std::string::npos,
        "foreground uses root's edge outputs, not an earlier transitive edge");
    auto window = campaign::web_graph(large, "test'run", 0, "");
    auto marker = "Remaining dependencies omitted (500-node limit).";
    auto pos = window.find(marker);
    check(pos != std::string::npos &&
              window.find(marker, pos + 1) == std::string::npos,
          "one truncation notice per window");
    check(window.find("data-name=\"bash-499\"") == std::string::npos &&
              window.find("Show next 500") != std::string::npos,
          "first graph window ends at its exact row boundary");
    auto next = campaign::web_graph(large, "test'run", 500, "");
    check(next.find("data-name=\"bash-499\"") != std::string::npos &&
              next.find("data-name=\"bash-500\"") != std::string::npos &&
              next.find("data-name=\"bash-498\"") == std::string::npos,
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
            "render reason SGR without exposing escape clutter");
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
    {
      campaign::Dataset ports{":memory:", true};
      json roots = json::array();
      for (unsigned i = 0; i < 300; ++i)
        roots.push_back({{"name", "port-" + std::to_string(i)},
                         {"drv", "/store/port.drv"}});
      json cohort = {
          {"id", "all-ports"}, {"name", "All ports"}, {"roots", roots}};
      for (unsigned i = 0; i < 300; ++i) {
        auto e = [&](unsigned n, std::string kind, json payload) {
          auto item = event(n, kind, payload);
          item["run"] = "port-" + std::to_string(i);
          return item;
        };
        ports.append(json::array(
            {e(1, "run.requested",
               {{"drv", "/store/port.drv"},
                {"store", "test"},
                {"index", i},
                {"cohort", cohort}}),
             e(2, "nix.build-result",
               {{"success", i != 298},
                {"outcome", i == 298 ? "failed" : "built"},
                {"outputs",
                 json::array(
                     {{{"path", "/store/verified"}, {"valid", true}},
                      {{"path", "/store/absent"}, {"valid", false}}})}})}));
        if (i == 0)
          check(ports.publication_outputs().at("paths").empty(),
                "worker result alone must not qualify for publication");
        if (i != 299)
          ports.append(json::array(
              {e(3, "run.finished",
                 {{"exited", true}, {"exit_code", i == 298 ? 1 : 0}})}));
      }
      check(
          ports.publication_outputs().at("paths") ==
              json::array({"/store/verified"}),
          "publication deduplicates only complete successful verified outputs");
      auto all = ports.view("", "", false);
      check(all.at("sessions").size() == 300 &&
                all.at("cohort").at("succeeded") == 298,
            "full port cohorts retain summaries beyond the standalone "
            "256-session limit");
    }
    std::cout << "transaction rollback, binary output, cursor, unknown events "
                 "and HTMX structure passed\n";
  } catch (const std::exception &e) {
    std::cerr << e.what() << '\n';
    return 1;
  }
}

// This process owns Nix's global state and blocking API. No Nix coroutine
// or logger callback ever enters the coordinator's cooperative NXT deck.
#ifdef unix
#undef unix
#endif

#include "journal.hh"

#include <nix/main/shared.hh>
#include <nix/store/build-result.hh>
#include <nix/store/derivations.hh>
#include <nix/store/globals.hh>
#include <nix/store/store-api.hh>
#include <nix/store/store-open.hh>
#include <nix/util/logging.hh>

#include <mutex>
#include <set>
#include <sstream>
#include <sys/prctl.h>

using campaign::json;

namespace {

class EventLogger final : public nix::Logger {
public:
  void emit(std::string kind, json payload) {
    std::lock_guard lock(mutex_);
    json event = {
        {"kind", std::move(kind)},
        {"payload", std::move(payload)},
        {"captured_wall_ns", campaign::wall_ns()},
        {"captured_mono_ns", campaign::monotonic_ns()},
    };
    // Blocking pipe writes provide bounded backpressure. If the recorder
    // disappears, terminate rather than throw from a logger destructor.
    try {
      campaign::write_all(3, event.dump() + "\n");
    } catch (...) {
      _exit(74);
    }
  }

  bool isVerbose() override { return true; }
  void log(nix::Verbosity level, std::string_view text) override {
    emit("nix.message", {{"level", level}, {"text_hex", campaign::hex(text)}});
  }
  void writeToStdout(std::string_view text) override {
    emit("nix.stdout", {{"text_hex", campaign::hex(text)}});
  }
  void logEI(const nix::ErrorInfo &error) override {
    std::ostringstream text;
    nix::showErrorInfo(text, error, true);
    emit("nix.error",
         {{"level", error.level}, {"text_hex", campaign::hex(text.str())}});
  }
  void startActivity(nix::ActivityId id, nix::Verbosity level,
                     nix::ActivityType type, const std::string &text,
                     const Fields &fields, nix::ActivityId parent) override {
    json payload = {
        {"id", id},
        {"parent", parent},
        {"type", type},
        {"level", level},
        {"text_hex", campaign::hex(text)},
        {"fields", encode(fields)},
    };
    // Nix 2.34.8's actBuild contract is [drv:string, machine:string,
    // outputs:int, outputsDone:int]. Retain the typed fields above, and
    // only normalize the two string fields when the contract matches.
    if (type == nix::actBuild && fields.size() == 4 &&
        fields[0].type == nix::Logger::Field::tString &&
        fields[1].type == nix::Logger::Field::tString &&
        fields[2].type == nix::Logger::Field::tInt &&
        fields[3].type == nix::Logger::Field::tInt) {
      payload["drv"] = fields[0].s;
      payload["machine"] = fields[1].s;
    }
    emit("nix.activity-started", std::move(payload));
  }
  void stopActivity(nix::ActivityId id) override {
    emit("nix.activity-stopped", {{"id", id}});
  }
  void result(nix::ActivityId id, nix::ResultType type,
              const Fields &fields) override {
    // Preserve EVERY result type, including unknown future Nix records.
    emit("nix.result",
         {
             {"id", id},
             {"type", type},
             {"fields", encode(fields)},
             {"build_output",
              type == nix::resBuildLogLine || type == nix::resPostBuildLogLine},
         });
  }

private:
  std::mutex mutex_;
  static json encode(const Fields &fields) {
    json result = json::array();
    for (const auto &field : fields) {
      if (field.type == nix::Logger::Field::tString)
        result.push_back({{"string_hex", campaign::hex(field.s)}});
      else
        result.push_back({{"integer", field.i}});
    }
    return result;
  }
};

std::string outcome(nix::BuildResultSuccessStatus status) {
  using S = nix::BuildResultSuccessStatus;
  switch (status) {
  case S::Built:
    return "built";
  case S::Substituted:
    return "substituted";
  case S::AlreadyValid:
    return "already-valid";
  case S::ResolvesToAlreadyValid:
    return "resolves-to-already-valid";
  }
  throw std::runtime_error("unknown Nix success status");
}

} // namespace

int main(int argc, char **argv) {
  if (argc != 4)
    return 2;
  // A recorder crash must not leave an unsupervised build client behind.
  auto parent = static_cast<pid_t>(std::stoi(argv[3]));
  if (::prctl(PR_SET_PDEATHSIG, SIGTERM) != 0)
    return 2;
  if (::getppid() != parent || parent == 1)
    return 2;
  auto events = std::make_unique<EventLogger>();
  auto &logger = *events;
  nix::logger = std::move(events);
  try {
    logger.emit("worker.started",
                {{"pid", ::getpid()}, {"library", NIX_LIBRARY_VERSION}});
    nix::initNix();
    auto store = nix::openStore(argv[2]);
    auto drv = store->parseStorePath(argv[1]);
    if (!drv.isDerivation())
      throw std::runtime_error("record requires a .drv path");
    auto recipe = store->readDerivation(drv);
    logger.emit("recipe.resolved",
                {
                    {"drv", store->printStorePath(drv)},
                    {"name", recipe.name},
                    {"system", recipe.platform},
                    {"input_derivation_roots", recipe.inputDrvs.map.size()},
                });
    std::set<std::string> discovered;
    auto discover = [&](auto &&self, const nix::StorePath &path) -> void {
      auto drvPath = store->printStorePath(path);
      if (!discovered.insert(drvPath).second)
        return;

      nix::Derivation derivation;
      try {
        derivation = store->readDerivation(path);
      } catch (const std::exception &) {
        // Input derivations may not be present in this store. Graph
        // discovery is observational and must not prevent the build.
        return;
      }

      json inputs = json::array();
      for (const auto &[inputPath, node] : derivation.inputDrvs.map) {
        json outputs = json::array();
        for (const auto &output : node.value)
          outputs.push_back(output);
        inputs.push_back({
            {"drv", store->printStorePath(inputPath)},
            {"outputs", std::move(outputs)},
            {"dynamic", !node.childMap.empty()},
        });
      }
      logger.emit("recipe.discovered", {{"drv", drvPath},
                                        {"name", derivation.name},
                                        {"system", derivation.platform},
                                        {"inputs", std::move(inputs)}});

      for (const auto &[inputPath, _] : derivation.inputDrvs.map)
        self(self, inputPath);
    };
    discover(discover, drv);
    nix::DerivedPath target = nix::DerivedPath::Built{
        .drvPath = nix::makeConstantStorePathRef(drv),
        .outputs = nix::OutputsSpec::All{},
    };
    auto results = store->buildPathsWithResults({target});
    const auto &result = results.at(0);
    const auto *success = result.tryGetSuccess();
    json outputs = json::array();
    bool valid = true;
    if (success) {
      for (const auto &[id, realised] : success->builtOutputs) {
        bool present = store->isValidPath(realised.outPath);
        outputs.push_back({{"path", store->printStorePath(realised.outPath)},
                           {"valid", present}});
        valid &= present;
      }
      valid &= !outputs.empty();
    }
    logger.emit(
        "nix.build-result",
        {
            {"drv", argv[1]},
            {"success", success && valid},
            {"outcome", success && valid ? outcome(success->status) : "failed"},
            {"outputs", outputs},
            {"result", json(result)},
        });
    return success && valid ? 0 : 1;
  } catch (const std::exception &error) {
    logger.emit("worker.error", {{"text_hex", campaign::hex(error.what())}});
    return 2;
  }
}

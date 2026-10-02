#include "journal.hh"

namespace campaign {

void Projection::apply(const json &event) {
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

json Projection::summary() const {
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

} // namespace campaign

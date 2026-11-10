#!/usr/bin/env python3
"""Pinned-input compile-cost guardrail on swa (docs/perf.md).

Measure plain, -O and the opt-in slow-call experiment from one saved compiler
state. --budget checks both a frozen optimized baseline and same-run ratios;
without it this records calibration data, never a passing budget verdict.
Run separately from the runtime gate. Inputs come from compile.nix.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import random
import signal
import statistics
import subprocess
import tempfile
import time


def measure(command, env, cpu, timeout):
    with tempfile.TemporaryDirectory() as work:
        timing = Path(work) / "time"
        with open(Path(work) / "stderr", "w+") as errors:
            p = subprocess.Popen(
                ["/usr/bin/time", "-f", "%U %S %M", "-o", str(timing),
                 "taskset", "-c", str(cpu), *command],
                env=env, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                stderr=errors, start_new_session=True)
            start = time.monotonic()
            try:
                p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
                raise RuntimeError(f"compile exceeded {timeout}s: {command}")
            if p.returncode:
                errors.seek(0)
                raise RuntimeError(f"compile exit {p.returncode}: {command}\n{errors.read()}")
            user, system, rss = map(float, timing.read_text().split())
            return {"user_s": user, "sys_s": system,
                    "wall_s": time.monotonic() - start, "peak_rss_kb": int(rss)}


def violations(result, budget):
    errors = []
    if result["cpu_model"] != budget["cpu_model"] or result["cpu"] != budget["cpu"]:
        errors.append("frozen timings require the calibrated CPU model and core")
    for name, case in result["cases"].items():
        frozen = budget["cases"][name]
        if case["sha256"] != frozen["sha256"]:
            errors.append(f"{name}: input differs from the frozen baseline")
        med = {m: statistics.median(x["user_s"] for x in xs)
               for m, xs in case["samples"].items()}
        for mode in ("O", "O-slow"):
            if med[mode] > budget["optimized_over_plain"] * med["plain"]:
                errors.append(f"{name}/{mode}: optimized/plain CPU budget exceeded")
            if med[mode] > budget["frozen_multiplier"] * frozen["O_user_s"]:
                errors.append(f"{name}/{mode}: frozen optimized CPU budget exceeded")
        if med["O-slow"] > budget["candidate_over_O"] * med["O"]:
            errors.append(f"{name}/O-slow: candidate/reference CPU budget exceeded")
        for mode, samples in case["samples"].items():
            if max(x["peak_rss_kb"] for x in samples) > budget["peak_rss_kb"]:
                errors.append(f"{name}/{mode}: peak RSS budget exceeded")
    return errors


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--budget", type=Path)
    ap.add_argument("--json", type=Path, required=True)
    ap.add_argument("--cpu", type=int, default=14)
    ap.add_argument("--trials", type=int, default=3)
    ap.add_argument("--modes", default="plain,O,O-slow")
    a = ap.parse_args()
    budget = json.loads(a.budget.read_text()) if a.budget else None
    modes = {"plain": [], "O": ["-O", "--slow-calls=reference"],
             "O-slow": ["-O", "--slow-calls=save"]}
    # Calibration also works before the new CLI option exists.
    if not budget:
        modes["O"] = ["-O"]
    chosen = a.modes.split(",")
    if budget and set(chosen) != set(modes):
        ap.error("a budget verdict requires plain,O,O-slow")
    if a.trials < 3:
        ap.error("at least three trials are required")
    env = {k: v for k, v in os.environ.items() if not k.startswith("NANOFIL_")}
    stack_limit = budget["stack_limit_bytes"] if budget else 4000000000
    env["NANOFIL_STACK_LIMIT"] = str(stack_limit)
    compiler = Path(__file__).resolve().parents[1] / "bin/nanofil"
    model = next(x.split(":", 1)[1].strip() for x in Path("/proc/cpuinfo").read_text().splitlines()
                 if x.startswith("model name"))
    if budget and (model != budget["cpu_model"] or a.cpu != budget["cpu"]):
        ap.error("frozen timings require the calibrated CPU model and core")
    sources = compiler.parent.parent / "src"
    digest = hashlib.sha256()
    for source in [compiler, *sorted(sources.rglob("*.pl"))]:
        digest.update(str(source.relative_to(compiler.parent.parent)).encode())
        digest.update(source.read_bytes())
    result = {"cpu": a.cpu, "cpu_model": model, "trials": a.trials,
              "stack_limit_bytes": stack_limit, "cases": {},
              "compiler_sha256": digest.hexdigest(),
              "source_revision": subprocess.check_output(
                  ["git", "rev-parse", "HEAD"], cwd=sources, text=True).strip(),
              "started_utc": datetime.now(timezone.utc).isoformat()}
    with tempfile.TemporaryDirectory() as work:
        state = Path(work) / "compiler.state"
        subprocess.run([str(compiler), "--save-state", str(state)], env=env, check=True,
                       stdin=subprocess.DEVNULL)
        env["NANOFIL_STATE"] = str(state)
        rng = random.Random(20261110)
        for name in ("compress", "lvm", "sqlite3"):
            source = (a.inputs / f"{name}.i").resolve()
            case = {"input": str(source), "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                    "samples": {m: [] for m in chosen}}
            if budget and case["sha256"] != budget["cases"][name]["sha256"]:
                ap.error(f"{name}: input differs from the frozen baseline")
            result["cases"][name] = case
            for trial in range(a.trials):
                order = rng.sample(chosen, len(chosen))
                for mode in order:
                    sample = measure([str(compiler), *modes[mode], "cc", str(source)], env,
                                     a.cpu, budget["wall_timeout_s"] if budget else 600)
                    case["samples"][mode].append(sample)
                    print(f"{name} {mode} trial {trial + 1}: {sample}", flush=True)
                    a.json.write_text(json.dumps(result, indent=2) + "\n")
    errors = violations(result, budget) if budget else []
    result["verdict"] = "FAIL" if errors else ("PASS" if budget else "calibration only")
    result["violations"] = errors
    result["finished_utc"] = datetime.now(timezone.utc).isoformat()
    a.json.write_text(json.dumps(result, indent=2) + "\n")
    print(result["verdict"], *errors, sep="\n", flush=True)
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())

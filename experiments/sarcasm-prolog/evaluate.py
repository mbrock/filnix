"""Reproduce correctness gates, code sizes, frontend timings and runtime samples.

Only checked C and the pinned upstream assembler are used for Fil-C code.
Native variants are valid-input baselines. Timing never runs in the Nix check.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import re
import resource
import shutil
import statistics
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
for name in ["translator", "filcc", "sarcasm"]:
    parser.add_argument("--" + name, required=True)
for name, default in [("cc", "cc"), ("assembler", "as"), ("nm", "nm"),
                      ("objdump", "objdump"), ("perf", "perf")]:
    parser.add_argument("--" + name, default=default)
parser.add_argument("--out", required=True, type=Path)
parser.add_argument("--check-only", action="store_true")
parser.add_argument("--core-revision")
parser.add_argument("--cpu", type=int)
parser.add_argument("--rounds", type=int, default=9)
parser.add_argument("--seconds", type=float, default=0.15)
args = parser.parse_args()
assert args.rounds >= 3 and args.seconds > 0
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
source = Path(__file__).resolve().parent
out = args.out.resolve()
out.mkdir(parents=True, exist_ok=True)
tools = {name: str(Path(shutil.which(getattr(args, name)) or getattr(args, name)).absolute())
         for name in ["translator", "filcc", "sarcasm", "cc", "assembler", "nm", "objdump", "perf"]}
commands = []


def run(command, *, cwd=out, env=None, check=True, limit=60):
    start = time.monotonic()
    result = subprocess.run([str(x) for x in command], cwd=cwd, env=env,
                            capture_output=True, text=True, timeout=limit)
    commands.append({"argv": [str(x) for x in command], "cwd": str(cwd),
                     "seconds": time.monotonic() - start, "exit": result.returncode})
    if check and result.returncode:
        raise RuntimeError((command, result.returncode, result.stdout, result.stderr))
    return result


def save(name, value):
    (out / name).write_text(json.dumps(value, indent=2) + "\n")


inputs = [source / "examples" / (name + ".s") for name in ["table-entry", "decoder", "loops"]]
assembly = "\n".join(p.read_text() for p in inputs)
(out / "input.s").write_text(assembly)
# Adapt annotation spelling only. Validate the exact pointer shapes rather
# than treating any annotation as sufficient evidence of a load or store.
counts = {"load": 0, "store": 0}
adapted = []
for line in assembly.splitlines():
    if "#! ptr" in line:
        body, tail = line.split("#! ptr")
        assert not tail.strip()
        if re.fullmatch(r"\s*movq\s+.*\),\s*%r\w+\s*", body):
            direction = "load"
        else:
            assert re.fullmatch(r"\s*movq\s+%r\w+,\s*.*\)\s*", body), body
            direction = "store"
        counts[direction] += 1
        line = body + "#! " + direction + " ptr"
    code, marker, comment = line.partition("#")
    if ";" in code:
        # The table fixture has two loads on one line. Upstream requires one
        # statement per line; do not split strings, comments or annotations.
        assert '"' not in code and not comment.startswith("!"), line
        parts = code.split(";")
        adapted.extend(parts[:-1])
        adapted.append(parts[-1] + marker + comment)
    else:
        adapted.append(line)
assert counts == {"load": 4, "store": 2}, counts
(out / "upstream-input.s").write_text("\n".join(adapted) + "\n")
roundtrip = "\n".join(adapted).replace("#! load ptr", "#! ptr").replace("#! store ptr", "#! ptr")
(out / "adapter-check.s").write_text(roundtrip + "\n")
original_effects = run([tools["translator"], "--emit-effects", out / "input.s"]).stdout
adapted_effects = run([tools["translator"], "--emit-effects", out / "adapter-check.s"]).stdout
def unlocated(text):
    return re.sub(r"located\(\d+,", "located(", text)
assert unlocated(original_effects) == unlocated(adapted_effects), "adapter changed instruction effects"
options = {
    "plain": ["--no-coalesce", "--no-simplify-conditions"],
    "groups": ["--no-simplify-conditions"],
    "conditions": ["--no-coalesce"],
    "optimized": [],
}
modes = ["filc-c", "filc-memcpy", *options, "upstream", "native-c", "native-asm"]
symbols = ["table_entry", "tiny_decode", "loop_walk"]
sizes = {}
gates = {}
for mode in modes:
    directory = out / mode
    directory.mkdir(exist_ok=True)
    native = mode.startswith("native-")
    compiler = tools["cc"] if native else tools["filcc"]
    if mode in options:
        result = run([tools["translator"], *options[mode], out / "input.s"])
        (directory / "output.s").write_text(result.stdout)
        result = run([tools["translator"], *options[mode], "--emit-c", out / "input.s"])
        (directory / "output.c").write_text(result.stdout)
    elif mode == "upstream":
        run([tools["sarcasm"], "--x86_64", "-S", out / "upstream-input.s", "-o", directory / "output.s"])
    elif mode.endswith("-c") or mode == "filc-memcpy":
        extra = [] if native else ["-fno-addrsig"]
        if mode == "filc-memcpy":
            extra += ["-DPACKED"]
        run([compiler, "-O2", *extra, "-S", source / "evaluation-reference.c", "-o", directory / "output.s"])
    else:
        (directory / "output.s").write_text(assembly)
    run([tools["assembler"], directory / "output.s", "-o", directory / "output.o"])
    run([compiler, "-O2", source / "evaluation-runtime.c", directory / "output.o", "-o", directory / "bench"])
    metadata = run([tools["nm"], "-S", directory / "output.o"]).stdout
    (directory / "symbols.txt").write_text(metadata)
    (directory / "disassembly.txt").write_text(run([tools["objdump"], "-dr", directory / "output.o"]).stdout)
    sizes[mode] = {}
    for name in symbols:
        pattern = name if native else r"pizlonatedFIP\d+_" + name
        found = re.search(r"^[0-9a-f]+\s+([0-9a-f]+)\s+[Tt]\s+" + pattern + r"$", metadata, re.M)
        assert found, (mode, name, metadata)
        sizes[mode][name] = int(found[1], 16)
    aligned = ["-DALIGNED_ONLY"] if mode == "upstream" else []
    run([compiler, "-O2", "-DNATIVE", *aligned, source / "decoder-runtime.c", directory / "output.o",
         "-o", directory / "decoder-runtime"])
    log = run([directory / "decoder-runtime"]).stdout
    log += run([directory / "bench", "table-check", "1"]).stdout
    unaligned = run([directory / "bench", "unaligned", "1"], check=False)
    if mode == "upstream":
        assert unaligned.returncode != 0 and "alignment requirement" in unaligned.stderr, unaligned
        (directory / "unaligned-rejection.txt").write_text(unaligned.stderr)
    else:
        assert unaligned.returncode == 0, unaligned
        log += unaligned.stdout
    if not native:
        log += run([sys.executable, source / "decoder-safety.py"], cwd=directory).stdout
        for failure in ["table-null", "table-tail", "table-freed"]:
            result = run([directory / "bench", failure, "1"], check=False)
            assert result.returncode != 0 and "filc safety error" in result.stderr, (mode, failure, result)
            (directory / (failure + ".txt")).write_text(result.stderr)
    gates[mode] = log.splitlines()
    print(mode, "correctness and applicable safety gates passed", flush=True)

manifest = {
    "tools": tools, "prolog_options": options, "code_bytes": sizes, "gates": gates,
    "tool_realpaths": {k: str(Path(v).resolve()) for k, v in tools.items()},
    "sources_sha256": {str(p.relative_to(source)): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in sorted(source.rglob("*")) if p.is_file() and p.suffix in [".pl", ".py", ".c", ".h", ".s"]},
    "annotation_changes": counts, "adapter_effects_equal": True,
    "code_metric": "fast entrypoint symbol size including its cold blocks; excludes getter and signature bridge",
}
pin = source.parent.parent / "lib" / "filc-upstream.json"
manifest["core_revision"] = args.core_revision or (json.loads(pin.read_text())["coreRev"] if pin.exists() else None)
save("build.json", {**manifest, "commands": commands})
if args.check_only:
    print("evaluation gates: ok", flush=True)
    sys.exit(0)

available = os.sched_getaffinity(0)
cpu = args.cpu if args.cpu is not None else min(available)
assert cpu in available
os.sched_setaffinity(0, {cpu})
topology = Path(f"/sys/devices/system/cpu/cpu{cpu}")
host = {"uname": platform.uname()._asdict(), "cpu": cpu, "available_cpus": sorted(available),
        "cpuinfo": Path("/proc/cpuinfo").read_text(), "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
for name in ["topology/thread_siblings_list", "cache/index3/size", "cache/index3/shared_cpu_list",
             "cpufreq/scaling_governor", "cpufreq/scaling_cur_freq"]:
    path = topology / name
    host[name] = path.read_text().strip() if path.exists() else None

# The front-end-only measurement ends at C; the end-to-end measurement
# includes Fil-C assembly emission. Upstream -S is an assembly emitter.
frontends = {}
jobs = [(m + "/c", [tools["translator"], *o, "--emit-c", out / "input.s"]) for m, o in options.items()]
jobs += [(m + "/assembly", [tools["translator"], *o, out / "input.s"]) for m, o in options.items()]
jobs += [("upstream/assembly", [tools["sarcasm"], "--x86_64", "-S", out / "upstream-input.s", "-o", out / "frontend-upstream.s"])]
random.Random(42).shuffle(jobs)
for trial in range(3):
    for name, command in jobs[trial:] + jobs[:trial]:
        run(command)
        frontends.setdefault(name, []).append(commands[-1]["seconds"])

workloads = {"table": (1000000, 1), "decode-small": (10000, 64), "decode": (20, 65536), "walk": (100, 4096)}
iterations = {}
for workload, (initial, units) in workloads.items():
    result = json.loads(run([out / "filc-memcpy" / "bench", workload, initial]).stdout)
    iterations[workload] = max(1, int(initial * args.seconds / max(result["seconds"], 1e-6)))
samples = []
order = modes.copy()
random.Random(42).shuffle(order)
for trial in range(args.rounds):
    for workload in workloads:
        for mode in order[trial % len(order):] + order[:trial % len(order)]:
            before = Path("/proc/loadavg").read_text().strip()
            result = json.loads(run([out / mode / "bench", workload, iterations[workload]]).stdout)
            samples.append({"trial": trial, "mode": mode, "workload": workload, "loadavg": before, **result})
    print(f"timing round {trial + 1}/{args.rounds}", flush=True)

events = "cycles,instructions,branches,branch-misses,cache-misses,context-switches,cpu-migrations"
perf = []
probe = (run([tools["perf"], "stat", "-e", events, "--", "true"], check=False)
         if Path(tools["perf"]).exists() else subprocess.CompletedProcess([], 127, "", "perf executable not found"))
if probe.returncode == 0:
    for name in ["control", "ack"]:
        path = out / name
        if path.exists():
            path.unlink()
        os.mkfifo(path)
    env = dict(os.environ, SP_PERF_CONTROL=str(out / "control"), SP_PERF_ACK=str(out / "ack"))
    for trial in range(2):
        for workload in workloads:
            for mode in (order if trial == 0 else list(reversed(order))):
                record = out / f"perf-{trial}-{workload}-{mode}.jsonl"
                result = run([tools["perf"], "stat", "--no-inherit", "-j", "-D", "-1", "--control",
                              f"fifo:{out}/control,{out}/ack", "-e", events, "-o", record, "--",
                              out / mode / "bench", workload, iterations[workload]], env=env)
                counters = [json.loads(line) for line in record.read_text().splitlines() if line.startswith("{")]
                perf.append({"trial": trial, "mode": mode, "workload": workload,
                             **json.loads(result.stdout), "counters": counters})
        print(f"counter round {trial + 1}/2", flush=True)
else:
    print("perf unavailable:", probe.stderr.strip(), flush=True)
summaries = {}
for workload, (_, units) in workloads.items():
    summaries[workload] = {}
    for mode in modes:
        rows = [r for r in samples if r["mode"] == mode and r["workload"] == workload]
        values = [r["seconds"] * 1e9 / r["iterations"] / units for r in rows]
        ratios = [r["seconds"] / next(b["seconds"] for b in samples if b["trial"] == r["trial"]
                  and b["workload"] == workload and b["mode"] == "filc-c") for r in rows]
        packed_ratios = [r["seconds"] / next(b["seconds"] for b in samples if b["trial"] == r["trial"]
                         and b["workload"] == workload and b["mode"] == "filc-memcpy") for r in rows]
        summaries[workload][mode] = {"median_ns_per_unit": statistics.median(values),
                                     "min": min(values), "max": max(values),
                                     "median_paired_ratio_to_filc_c": statistics.median(ratios),
                                     "median_paired_ratio_to_filc_memcpy": statistics.median(packed_ratios)}
save("results.json", {**manifest, "host": host, "rounds": args.rounds, "iterations": iterations,
                      "frontend_seconds": frontends, "samples": samples, "perf": perf,
                      "perf_unavailable": probe.stderr if probe.returncode else None,
                      "summaries": summaries, "commands": commands})
print(json.dumps(summaries, indent=2), flush=True)

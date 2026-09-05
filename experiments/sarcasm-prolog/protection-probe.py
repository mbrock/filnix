"""Inspect the pinned compiler without rebuilding it or disabling protection.

The metric is static conditional branches targeting compiler-labelled
access-failure blocks. It is neither a count of runtime-taken branches nor
a count of source loads. Retain assembly so these small cases can be audited.
"""
import json
from pathlib import Path
import re
import resource
import subprocess
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
compiler = sys.argv[1]
source = Path(__file__).with_name("protection-probe.c")
driver = source.with_name("protection-probe-runtime.c")
modes = {
    "default": [],
    "forward": ["-mllvm", "-filc-propagate-checks-backward=false"],
    "disabled": ["-mllvm", "-filc-optimize-checks=false"],
}
names = ["covering", "diamond", "one_path", "checked", "changed", "retained_loads", "call_barrier"]
metrics = {}
for mode, options in modes.items():
    assembly = Path(f"probe-{mode}.s")
    subprocess.run([compiler, "-O2", "-fno-addrsig", *options, "-S", str(source), "-o", str(assembly)],
                   check=True, timeout=30)
    subprocess.run([compiler, "-O2", *options, str(source), str(driver), "-o", f"probe-{mode}"],
                   check=True, timeout=30)
    subprocess.run([f"./probe-{mode}"], check=True, timeout=15)
    failed = subprocess.run([f"./probe-{mode}", "free"], capture_output=True, timeout=15)
    assert failed.returncode < 0 and b"filc safety error" in failed.stderr, (mode, failed)
    text = assembly.read_text()
    per_function = {}
    for name in names:
        match = re.search(r"^pizlonatedFIP\d+_" + name + r":.*?(?=^\.Lfunc_end\d+:)",
                          text, re.S | re.M)
        assert match, (mode, name)
        body = match.group(0)
        failures = set(re.findall(r"^(\.\w+):[^\n]*# %filc_range_fail_block[^\n]*", body, re.M))
        assert failures, (mode, name, "no labelled access-failure blocks")
        branches = re.findall(r"^\s+(j\w+)\s+(\.\w+)", body, re.M)
        per_function[name] = sum(op != "jmp" and target in failures for op, target in branches)
    metrics[mode] = per_function
    print(mode, per_function)

# Only the diagnostic scheduling optimization is disabled in the last mode;
# accesses remain instrumented and the post-call free test must still fail.
assert metrics["default"]["retained_loads"] < metrics["disabled"]["retained_loads"], metrics
assert metrics["default"]["call_barrier"] > metrics["default"]["retained_loads"], metrics
Path("metrics.json").write_text(json.dumps({
    "compiler": compiler,
    "metric": "static conditional branches to compiler-labelled access-failure blocks",
    "flags": modes, "counts": metrics,
}, indent=2) + "\n")

#!/usr/bin/env python3
"""Executed nanofil -O checks by what filcc's forward scheduling would do
with them (docs/perf.md item 16).

Runs checkclass.pl on every preprocessed source of a program (checks.nix's
`src` variant keeps them), then weighs each check that nanofil -O keeps
by its block's execution count in checks.py's callgrind run of the `O`
build: the count of the instruction at the block's label, which `as -L`
kept as a symbol. Prints, per workload, millions of executed checks by
nanofil's op (check, renew, check_local) and class (checkclass.pl's
header), by offset form and loop position, and the classes of the
hottest functions.

usage: checkclass.py [--builds DIR] [--src DIR] [--work DIR] [--only SUBSTR] [--top N]
Run checks.py first, with the same --work, for the O build's callgrind files.
"""
import argparse, collections, glob, json, os, re, subprocess
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("--builds", default=f"{HERE}/checks")
ap.add_argument("--src", default=None, help="checks.nix's src variant (default: --builds)")
ap.add_argument("--work", default="checks-work")
ap.add_argument("--only", default="")
ap.add_argument("--top", type=int, default=8)
ap.add_argument("--variant", default="O", help="the nanofil build whose block counts weigh the checks")
ap.add_argument("--json", default="checkclass.json")
a = ap.parse_args()
SRC = a.src or a.builds
NANOFIL = os.path.dirname(os.path.dirname(HERE))
WORKLOADS = {"zlib -6": "zlib", "zlib -d": "zlib", "bzip2 -9": "bzip2", "bzip2 -d": "bzip2",
             "lz4 -1": "lz4", "lz4 -9": "lz4", "lz4 -d": "lz4", "lua int": "lua", "lua tab": "lua",
             "lua str": "lua", "sqlite": "sqlite"}
WORKLOADS = {w: p for w, p in WORKLOADS.items() if a.only in w}
key = lambda w: re.sub(r"\W+", "-", w)


def classify(path):
    out = f"{a.work}/class.{os.path.basename(os.path.dirname(os.path.dirname(os.path.dirname(path))))}.{os.path.basename(path)}.tsv"
    if not os.path.exists(out):
        env = dict(os.environ, NANOFIL_STACK_LIMIT="8000000000")
        with open(out + ".tmp", "w") as o:
            subprocess.run([f"{NANOFIL}/bin/nanofil", "--script", f"{HERE}/checkclass.pl", os.path.realpath(path)],
                           cwd=f"{NANOFIL}/src", stdin=subprocess.DEVNULL, stdout=o, check=True, env=env)
        os.rename(out + ".tmp", out)
    return [line.rstrip("\n").split("\t") for line in open(out)]


progs = sorted(set(WORKLOADS.values()))
with ThreadPoolExecutor(max_workers=max(1, (os.cpu_count() or 2) // 2)) as ex:
    futs = {(p, f): ex.submit(classify, f) for p in progs for f in sorted(glob.glob(f"{SRC}/{p}/src/i/*.i"))}
    rows = {p: [] for p in progs}
    for (p, _), fut in futs.items():
        rows[p] += fut.result()


def exe_of(path):
    for line in open(path):
        if line.startswith("cmd:"):
            return line.split()[1]


def executed(path, exe):
    ir, skip, ob = collections.Counter(), False, None
    exe = os.path.realpath(exe)
    for line in open(path):
        if line.startswith("ob="):
            ob = os.path.realpath(line[3:].strip()); continue
        if line.startswith("calls="):
            skip = True; continue
        f = line.split()
        if len(f) == 3 and f[0].startswith("0x") and not skip and ob == exe:
            ir[int(f[0], 16)] += int(f[2])
        skip = False
    return ir


M = 1e6
report = {}
for w, prog in WORKLOADS.items():
    cg = f"{a.work}/cg.{a.variant}.{key(w)}"
    exe = exe_of(cg)
    ir = executed(cg, exe)
    labels = {}
    for line in subprocess.run(["nm", exe], capture_output=True, text=True, check=True).stdout.splitlines():
        f = line.split()
        if len(f) == 3 and f[2].startswith(".L"):
            labels.setdefault(f[2], int(f[0], 16))
    by = collections.Counter()
    byfn = collections.defaultdict(collections.Counter)
    missing = 0
    for fn, block, _, op, cls, off, loop, rights, use in rows[prog]:
        addr = labels.get(f".L{fn}.{block}")
        if addr is None:
            missing += 1
            continue
        n = ir.get(addr, 0)
        if not n:
            continue
        by[(op, cls, off, loop, use)] += n
        byfn[fn][(op, cls)] += n
    report[w] = {"classes": {"|".join(k): v for k, v in by.items()},
                 "functions": {f: {"|".join(k): v for k, v in c.items()} for f, c in byfn.items()},
                 "unmatched": missing}
    total = sum(v for (op, *_), v in by.items() if op != "check_local")
    report[w]["total"] = total
    print(f"\n{w}: {total / M:.1f}M heap checks and renewals ({missing} check lines without a block symbol)")
    agg = collections.Counter()
    for (op, cls, off, loop, use), v in by.items():
        agg[(op, cls)] += v
    for (op, cls), v in sorted(agg.items(), key=lambda kv: -kv[1]):
        if v > M / 10:
            print(f"  {op:12} {cls:14} {v / M:8.1f}M")
    print("  by offset form and loop (full checks only):")
    agg2 = collections.Counter()
    for (op, cls, off, loop, use), v in by.items():
        if op == "check":
            agg2[(cls, off, loop)] += v
    for (cls, off, loop), v in sorted(agg2.items(), key=lambda kv: -kv[1])[:14]:
        print(f"    {cls:14} {off:6} {loop:5} {v / M:8.1f}M")
    print("  covered and flags by consumer:")
    agg3 = collections.Counter()
    for (op, cls, off, loop, use), v in by.items():
        if cls.startswith(("covered", "flags")):
            agg3[(op, cls, use)] += v
    for (op, cls, use), v in sorted(agg3.items(), key=lambda kv: -kv[1]):
        if v > M / 10:
            print(f"    {op:8} {cls:14} {use:8} {v / M:8.1f}M")
    tot = {f: sum(c.values()) for f, c in byfn.items()}
    for f in sorted(tot, key=lambda f: -tot[f])[:a.top]:
        print(f"  {f:32} {tot[f] / M:7.1f}M " +
              ", ".join(f"{op} {cls} {v / M:.1f}" for (op, cls), v in byfn[f].most_common(5)))
json.dump(report, open(a.json, "w"))

#!/usr/bin/env python3
"""Where each build spends its cycles, per function (docs/perf.md item 19).

Samples every gate workload (and SWI-Prolog's suite, if ../swipl has the
builds) under `perf record -e {cycles:u,instructions:u}` on one pinned
CPU, repeating each run until it has taken about --seconds, then reads
`perf report --group` per symbol. Function names are reduced to their C
names (pizlonated..._f is f), so the native, filcc and nanofil builds
line up. Prints, per workload, the hottest functions with each build's
share of the cycles, its cycles per run and its IPC; shared objects
(the Fil-C runtime, libc) are one row each.

usage: hot.py [--builds DIR] [--variants native,ref,O] [--work DIR]
              [--only SUBSTR] [--cpu C] [--seconds S] [--top N] [--json FILE]
"""
import argparse, collections, json, os, re, subprocess, time

HERE = os.path.dirname(os.path.abspath(__file__))
L = os.path.dirname(HERE)
ap = argparse.ArgumentParser()
ap.add_argument("--builds", default=f"{L}/out")
ap.add_argument("--swipl", default=f"{L}/swipl")
ap.add_argument("--variants", default="native,ref,O")
ap.add_argument("--work", default="hot-work")
ap.add_argument("--only", default="")
ap.add_argument("--cpu", type=int, default=6)
ap.add_argument("--seconds", type=float, default=2.0, help="sample each workload for about this long")
ap.add_argument("--top", type=int, default=10)
ap.add_argument("--json", default="hot.json")
a = ap.parse_args()
os.makedirs(a.work, exist_ok=True)
B = a.builds
VARIANTS = a.variants.split(",")
TEXT, RANDOM = f"{B}/inputs/text", f"{B}/inputs/random"
EXE = {"zlib": "minigzip", "bzip2": "bzip2", "lz4": "lz4", "lua": "lua", "sqlite": "sqlite3"}


def ref_output(prog, args, src, name):
    path = f"{a.work}/{name}"
    if not os.path.exists(path):
        with open(src, "rb") as i, open(path, "wb") as o:
            subprocess.run([f"{B}/{prog}/ref/{EXE[prog]}", *args], stdin=i, stdout=o, check=True)
    return path


W = {
    "zlib -6": ("zlib", ["-6"], TEXT),
    "zlib -d": ("zlib", ["-d"], ref_output("zlib", ["-6"], TEXT, "text.gz")),
    "bzip2 -9": ("bzip2", ["-9"], TEXT),
    "bzip2 -d": ("bzip2", ["-d"], ref_output("bzip2", ["-9"], TEXT, "text.bz2")),
    "lz4 -1": ("lz4", ["-q", "-1"], RANDOM),
    "lz4 -9": ("lz4", ["-q", "-9"], TEXT),
    "lz4 -d": ("lz4", ["-q", "-d"], ref_output("lz4", ["-q", "-9"], TEXT, "text.lz4")),
    "lua int": ("lua", [f"{L}/int.lua"], None),
    "lua tab": ("lua", [f"{L}/tab.lua"], None),
    "lua str": ("lua", [f"{L}/str.lua"], None),
    "sqlite": ("sqlite", [], f"{L}/sqlite.sql"),
}
if all(os.path.isdir(f"{a.swipl}/{v}") for v in VARIANTS):
    W["swipl bench"] = ("swipl", [f"{L}/swipl.pl", f"{a.swipl}/bench", "0.02"], None)
W = {k: v for k, v in W.items() if a.only in k}
key = lambda w: re.sub(r"\W+", "-", w)


def command(w, v):
    prog, args, stdin = W[w]
    exe = f"{a.swipl}/{v}/swipl" if prog == "swipl" else f"{B}/{prog}/{v}/{EXE[prog]}"
    return [exe, *args], stdin


def name(sym):
    m = re.match(r"pizlonated(?:FIP?\d+)?_(.*)", sym)
    return m.group(1) if m else sym


def profile(w, v):
    """{function: (cycles, instructions)} per run of w under v, and the run count."""
    cmd, stdin = command(w, v)
    t0 = time.time()
    with open(stdin or os.devnull, "rb") as i:
        subprocess.run(cmd, stdin=i, stdout=subprocess.DEVNULL, check=True)
    runs = max(1, round(a.seconds / max(time.time() - t0, 1e-3)))
    data = f"{a.work}/perf.{v}.{key(w)}.data"
    loop = " ".join(f"'{x}'" for x in cmd)
    script = f"for i in $(seq {runs}); do {loop} <'{stdin or os.devnull}' >/dev/null; done"
    subprocess.run(["taskset", "-c", str(a.cpu), "perf", "record", "-q", "-F", "20000", "-e", "{cycles:u,instructions:u}",
                    "-o", data, "--", "sh", "-c", script], check=True, stderr=subprocess.DEVNULL)
    rep = subprocess.run(["perf", "report", "-i", data, "--stdio", "--group", "--no-children", "--sort", "dso,sym",
                          "--percent-limit", "0", "--percentage", "relative", "-F", "overhead,dso,sym", "--comm", os.path.basename(cmd[0])],
                         capture_output=True, text=True, check=True).stdout
    out = {}
    for line in rep.splitlines():
        if line.startswith("#") or not line.strip():
            continue
        m = re.match(r"\s*([\d.]+)%\s+([\d.]+)%\s+(\S+)\s+\[\.\]\s+(.*)$", line)
        if not m:
            continue
        dso, sym = m.group(3), m.group(4).strip()
        own = os.path.basename(cmd[0]) == dso or dso.startswith("libswipl")
        fn = name(sym) if own else f"[{re.sub(r'[.]so.*', '', dso)}]"
        add(out, fn, (float(m.group(1)), float(m.group(2))))
    # perf report gives shares; scale them with perf stat's totals of one run.
    st = subprocess.run(["taskset", "-c", str(a.cpu), "perf", "stat", "-x,", "-e", "cycles:u,instructions:u", "--", *cmd],
                        stdin=open(stdin or os.devnull, "rb"), stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                        text=True, check=True).stderr
    tot = {}
    for line in st.splitlines():
        f = line.split(",")
        if len(f) > 2 and f[0][:1].isdigit():
            tot[f[2].split(":")[0]] = float(f[0])
    return {fn: (c / 100 * tot["cycles"], i / 100 * tot["instructions"]) for fn, (c, i) in out.items()}, tot


def add(c, k, v):
    old = c.get(k, (0.0, 0.0))
    c[k] = (old[0] + v[0], old[1] + v[1])


results = {}
for w in W:
    for v in VARIANTS:
        fns, tot = profile(w, v)
        results[(w, v)] = {"functions": fns, "cycles": tot["cycles"], "instructions": tot["instructions"]}
json.dump({f"{w}|{v}": r for (w, v), r in results.items()}, open(a.json, "w"))

for w in W:
    print(f"\n{w}: hottest functions; per build: share of cycles, Mcycles per run, IPC")
    print("| function | " + " | ".join(VARIANTS) + " |\n|---|" + "--:|" * len(VARIANTS))
    rank = collections.Counter()
    for v in VARIANTS:
        for f, (c, _) in results[(w, v)]["functions"].items():
            rank[f] = max(rank[f], c)
    for f, _ in rank.most_common(a.top):
        cells = []
        for v in VARIANTS:
            r = results[(w, v)]
            c, i = r["functions"].get(f, (0.0, 0.0))
            cells.append(f"{100 * c / r['cycles']:.0f}%, {c / 1e6:.0f}, {i / c:.2f}" if c else "–")
        print(f"| {f} | " + " | ".join(cells) + " |")

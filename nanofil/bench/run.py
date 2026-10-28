#!/usr/bin/env python3
"""nanofil's runtime benchmark gate (docs/perf.md).

Runs every workload with every build in OUT (default: out/ next to this
file, built by default.nix): first once each, comparing stdout byte for
byte with the filcc -O2 build (`ref`), then TRIALS timed rounds after one
warm-up round. Within a round each workload runs every mode in a shuffled
order (seeded), pinned to one CPU under `perf stat`, which counts user
instructions and task-clock. Before each run it waits until the pinned
core and its SMT sibling are idle. Prints medians, ranges and ratios to
ref, and writes the samples to results.json in the current directory.

usage: run.py [--trials N] [--cpu C] [--out DIR] [--modes a,b] [--only SUBSTR]
"""
import argparse, hashlib, json, os, random, statistics, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("--trials", type=int, default=7)
ap.add_argument("--cpu", type=int, default=6)
ap.add_argument("--out", default=f"{HERE}/out")
ap.add_argument("--ref", default=f"{HERE}/ref",
                help="where the filcc builds come from (default ref/, else --out): pin them, filcc is not deterministic")
ap.add_argument("--modes", default="ref,off,O,O-reuse,O-refbranches,O-stack")
ap.add_argument("--only", default="")
ap.add_argument("--json", default="results.json")
ap.add_argument("--markdown", metavar="JSON", help="print tables of an earlier run's samples and exit")
ap.add_argument("--compare", metavar="LABEL=JSON[@MODE]", nargs="+",
                help="print each run's MODE (default --mode) ratios to ref and exit")
ap.add_argument("--mode", default="O", help="the mode --compare reports")
a = ap.parse_args()
if a.compare:
    import statistics as st
    runs = []
    for c in a.compare:
        label, rest = c.split("=", 1)
        path, _, mode = rest.partition("@")
        runs.append((label, json.load(open(path))["samples"], mode or a.mode))
    med = st.median
    print("time ratio to ref (instruction ratio); * marks a row whose trial times overlap the previous column's\n")
    print("| Workload | " + " | ".join(f"{l} `{m}`" for l, _, m in runs) + " |\n|---|" + "--:|" * len(runs))
    geo = [[] for _ in runs]
    for w in runs[0][1]:
        cells = []
        for k, (_, r, m) in enumerate(runs):
            d = r[w]
            t, i = (med(x[j] for x in d[m]) / med(x[j] for x in d["ref"]) for j in (1, 0))
            geo[k].append((t, i))
            ts = [x[1] for x in d[m]]
            mark = ""
            if k:
                ps = [x[1] for x in runs[k - 1][1][w][runs[k - 1][2]]]
                mark = "*" if max(ts) >= min(ps) and max(ps) >= min(ts) else ""
            cells.append(f"{t:.2f} ({i:.2f}){mark}")
        print(f"| {w} | " + " | ".join(cells) + " |")
    print("| geomean | " + " | ".join(
        f"{st.geometric_mean(t for t, _ in g):.2f} ({st.geometric_mean(i for _, i in g):.2f})" for g in geo) + " |")
    sys.exit()
if a.markdown:
    import statistics as st
    r = json.load(open(a.markdown))["samples"]
    ms = list(next(iter(r.values())))
    med = lambda xs: st.median(xs)
    print("| Workload | " + " | ".join(ms) + " |\n|---|" + "--:|" * len(ms))
    for w, d in r.items():
        print(f"| {w} | " + " | ".join(f"{med(t for _, t in d[m]):.1f} ms, {med(i for i, _ in d[m]) / 1e9:.2f}G" for m in ms) + " |")
    ns = [m for m in ms if m != "ref"]
    print("\n| Workload | " + " | ".join(ns) + " |\n|---|" + "--:|" * len(ns))
    ratio = lambda d, m, k: med(x[k] for x in d[m]) / med(x[k] for x in d["ref"])
    for w, d in r.items():
        print(f"| {w} | " + " | ".join(f"{ratio(d, m, 1):.2f} ({ratio(d, m, 0):.2f})" for m in ns) + " |")
    print("| geomean | " + " | ".join(
        f"{st.geometric_mean([ratio(d, m, 1) for d in r.values()]):.2f} "
        f"({st.geometric_mean([ratio(d, m, 0) for d in r.values()]):.2f})" for m in ns) + " |")
    sys.exit()
O = a.out
REF = a.ref if os.path.isdir(a.ref) else O
MODES = a.modes.split(",")
TEXT, RANDOM = f"{O}/inputs/text", f"{O}/inputs/random"
tmp = tempfile.mkdtemp(prefix="nanofil-bench-")


def ref_dir(prog):
    """Where prog's filcc build comes from: the pin if it has one."""
    return REF if os.path.isdir(f"{REF}/{prog}/ref") else O


def ref_output(prog, exe, args, src, name):
    path = f"{tmp}/{name}"
    with open(src, "rb") as i, open(path, "wb") as o:
        subprocess.run([f"{ref_dir(prog)}/{prog}/ref/{exe}", *args], stdin=i, stdout=o, check=True)
    return path


GZ = ref_output("zlib", "minigzip", ["-6"], TEXT, "text.gz")
BZ = ref_output("bzip2", "bzip2", ["-9"], TEXT, "text.bz2")
LZ = ref_output("lz4", "lz4", ["-q", "-9"], TEXT, "text.lz4")
LUA = lambda s: [f"{HERE}/{s}.lua"]
# name: (program, executable, arguments, stdin)
W = {
    "zlib -6 text": ("zlib", "minigzip", ["-6"], TEXT),
    "zlib -d text": ("zlib", "minigzip", ["-d"], GZ),
    "bzip2 -9 text": ("bzip2", "bzip2", ["-9"], TEXT),
    "bzip2 -d text": ("bzip2", "bzip2", ["-d"], BZ),
    "lz4 -1 random": ("lz4", "lz4", ["-q", "-1"], RANDOM),
    "lz4 -9 text": ("lz4", "lz4", ["-q", "-9"], TEXT),
    "lz4 -d text": ("lz4", "lz4", ["-q", "-d"], LZ),
    "lua int": ("lua", "lua", LUA("int"), None),
    "lua tab": ("lua", "lua", LUA("tab"), None),
    "lua str": ("lua", "lua", LUA("str"), None),
    "sqlite": ("sqlite", "sqlite3", [], f"{HERE}/sqlite.sql"),
}
W = {k: v for k, v in W.items() if a.only in k}


def cmd(w, m):
    prog, exe, args, _ = W[w]
    return [f"{ref_dir(prog) if m == 'ref' else O}/{prog}/{m}/{exe}", *args]


def stdin(w):
    return open(W[w][3] or os.devnull, "rb")


# Correctness first: every build's output is ref's, byte for byte.
for w in W:
    with stdin(w) as i:
        want = subprocess.run(cmd(w, "ref"), stdin=i, capture_output=True, check=True).stdout
    for m in MODES:
        with stdin(w) as i:
            got = subprocess.run(cmd(w, m), stdin=i, capture_output=True, check=True).stdout
        if got != want:
            sys.exit(f"{w}: {m} differs from ref ({len(got)} vs {len(want)} bytes)")
    print(f"ok {w}: {len(want)} bytes, sha256 {hashlib.sha256(want).hexdigest()[:16]}", file=sys.stderr)


def siblings(cpu):
    p = f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list"
    s = open(p).read().strip()
    out = set()
    for part in s.split(","):
        lo, _, hi = part.partition("-")
        out.update(range(int(lo), int(hi or lo) + 1))
    return out


def busy(cpus):
    def snap():
        r = {}
        for line in open("/proc/stat"):
            f = line.split()
            if f[0].startswith("cpu") and f[0][3:].isdigit() and int(f[0][3:]) in cpus:
                v = list(map(int, f[1:]))
                r[f[0]] = (sum(v) - v[3] - v[4], sum(v))
        return r
    s0 = snap(); time.sleep(0.2); s1 = snap()
    return max((s1[c][0] - s0[c][0]) / max(1, s1[c][1] - s0[c][1]) for c in s0)


CORE = siblings(a.cpu)
waited = 0


def quiet():
    global waited
    while busy(CORE) > 0.05:
        waited += 1
        time.sleep(1)


def measure(w, m):
    quiet()
    c = ["taskset", "-c", str(a.cpu), "perf", "stat", "-x,", "-e", "instructions:u,task-clock", *cmd(w, m)]
    with stdin(w) as i:
        p = subprocess.run(c, stdin=i, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, check=True)
    v = {}
    for line in p.stderr.splitlines():
        f = line.split(",")
        if len(f) > 2 and f[0][:1].isdigit():
            v[f[2].split(":")[0]] = float(f[0])
    return v["instructions"], v["task-clock"]


print(f"ref {os.path.realpath(REF)}", file=sys.stderr)
print(f"loadavg {open('/proc/loadavg').read().split()[:3]}, cpu {a.cpu} (siblings {sorted(CORE)})", file=sys.stderr)
rng = random.Random(1)
res = {w: {m: [] for m in MODES} for w in W}
for trial in range(a.trials + 1):  # round 0 warms up and is discarded
    for w in W:
        order = MODES[:]
        rng.shuffle(order)
        for m in order:
            s = measure(w, m)
            if trial:
                res[w][m].append(s)
    print(f"round {trial}/{a.trials} done", file=sys.stderr)
json.dump({"trials": a.trials, "cpu": a.cpu, "samples": res}, open(a.json, "w"), indent=1)

med = statistics.median
print(f"median task-clock ms and user instructions (G), {a.trials} trials, cpu {a.cpu}; waited {waited} s for a quiet core")
print(f"{'workload':15}" + "".join(f"{m:>19}" for m in MODES))
for w in W:
    row = f"{w:15}"
    for m in MODES:
        row += f"{med(t for _, t in res[w][m]):10.1f} {med(i for i, _ in res[w][m]) / 1e9:7.2f}G"
    print(row)
print("\nratio to ref: time (instructions); range is the trials' min..max time ratio to ref's median")
print(f"{'workload':15}" + "".join(f"{m:>24}" for m in MODES if m != "ref"))
for w in W:
    rt = med(t for _, t in res[w]["ref"]); ri = med(i for i, _ in res[w]["ref"])
    row = f"{w:15}"
    for m in MODES:
        if m == "ref":
            continue
        ts = [t for _, t in res[w][m]]
        row += f"{med(ts) / rt:6.2f} ({med(i for i, _ in res[w][m]) / ri:5.2f}) {min(ts) / rt:5.2f}..{max(ts) / rt:<5.2f}"
    print(row)
geo = lambda xs: statistics.geometric_mean(xs)
print(f"{'geomean':15}" + "".join(
    f"{geo([med(t for _, t in res[w][m]) / med(t for _, t in res[w]['ref']) for w in W]):6.2f} "
    f"({geo([med(i for i, _ in res[w][m]) / med(i for i, _ in res[w]['ref']) for w in W]):5.2f}){'':12}"
    for m in MODES if m != "ref"))

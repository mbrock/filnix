#!/usr/bin/env python3
"""Attribute nanofil's executed instructions to categories (docs/perf.md).

Runs each benchmark workload under cachegrind with the marked build
(default.nix here, `out/`) and with the filcc build (the gate's
`../out/<prog>/ref`), then classifies every executed line of the marked
.s by the marker labels before it and its own form. Prints a table of
categories per workload, the share of const-compare blocks, and the
hottest functions against filcc's. A const-compare block only
compares a value with a constant and branches: an upper bound on switch
dispatch.

usage: profile.py [--marked DIR] [--bench DIR] [--work DIR] [--only SUBSTR]
Needs valgrind on PATH or in $VALGRIND.
"""
import argparse, collections, glob, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("--marked", default=f"{HERE}/out")
ap.add_argument("--bench", default=f"{HERE}/../out")
ap.add_argument("--ref", default=f"{HERE}/../ref")
ap.add_argument("--work", default="profile-work")
ap.add_argument("--only", default="")
a = ap.parse_args()
os.makedirs(a.work, exist_ok=True)
B, M, L = a.bench, a.marked, os.path.dirname(HERE)
R = a.ref if os.path.isdir(a.ref) else B
TEXT, RANDOM = f"{B}/inputs/text", f"{B}/inputs/random"
EXE = {"zlib": "minigzip", "bzip2": "bzip2", "lz4": "lz4", "lua": "lua"}


def ref_output(prog, args, src, name):
    path = f"{a.work}/{name}"
    with open(src, "rb") as i, open(path, "wb") as o:
        subprocess.run([f"{R}/{prog}/ref/{EXE[prog]}", *args], stdin=i, stdout=o, check=True)
    return path


W = {
    "zlib -6 text": ("zlib", ["-6"], TEXT),
    "zlib -d text": ("zlib", ["-d"], ref_output("zlib", ["-6"], TEXT, "text.gz")),
    "bzip2 -9 text": ("bzip2", ["-9"], TEXT),
    "bzip2 -d text": ("bzip2", ["-d"], ref_output("bzip2", ["-9"], TEXT, "text.bz2")),
    "lz4 -1 random": ("lz4", ["-q", "-1"], RANDOM),
    "lz4 -9 text": ("lz4", ["-q", "-9"], TEXT),
    "lz4 -d text": ("lz4", ["-q", "-d"], ref_output("lz4", ["-q", "-9"], TEXT, "text.lz4")),
    "lua int": ("lua", [f"{L}/int.lua"], None),
    "lua tab": ("lua", [f"{L}/tab.lua"], None),
    "lua str": ("lua", [f"{L}/str.lua"], None),
}
W = {k: v for k, v in W.items() if a.only in k}
key = lambda w: re.sub(r"\W+", "-", w)


def cachegrind(w, variant):
    prog, args, stdin = W[w]
    exe = f"{M}/{prog}/{EXE[prog]}" if variant == "nf" else f"{R}/{prog}/ref/{EXE[prog]}"
    out = f"{a.work}/cg.{variant}.{key(w)}"
    # Fil-C's ioctl wrapper asserts an integer argument below 4 GiB is not
    # a heap pointer; valgrind would otherwise put the heap there.
    cmd = [os.environ.get("VALGRIND", "valgrind"), "--aspace-minaddr=0x100000000", "--tool=cachegrind",
           "--cache-sim=no", f"--cachegrind-out-file={out}", exe, *args]
    with open(stdin or os.devnull, "rb") as i:
        subprocess.run(cmd, stdin=i, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
    return out


with ThreadPoolExecutor(max_workers=os.cpu_count() // 2) as ex:
    runs = {(w, v): ex.submit(cachegrind, w, v) for w in W for v in ("nf", "ref")}
    files = {k: f.result() for k, f in runs.items()}

INS = re.compile(r"^\t([a-z][a-z0-9]*)\s*(.*)$")
REGION = re.compile(r"^\.Lpf\.R\.([A-Za-z0-9_]+)\.\d+:$")
SLOT = re.compile(r"^\.Lpf\.S\.([A-Za-z0-9_]+)\.\d+:$")
FUNC = re.compile(r"^([A-Za-z_][A-Za-z0-9_.$]*):$")
RBP = re.compile(r"-?\d*\(%rbp\)")
POINTER_REGIONS = ("flight", "chk_ptr", "reused", "phi_p", "acc_raw_load_pointer_p", "acc_raw_store_pointer")
CALL_TEMPS = ("abi_receive", "abi_result", "abi_invoke", "abi_return_value", "abi_dispatch")


def classify(region, slot, op, args, fn):
    """(category, subcategory) of one emitted instruction."""
    rbp = bool(RBP.search(args)) and not op.startswith("lea")
    if not fn.startswith("pizlonatedFIP"):
        return "calls", "getter/adapter/thunk"
    if region in ("cold", "exc_exit"):
        return "calls", region
    if region == "prologue" or region.startswith("abi_"):
        if slot == "lower":
            return "lowers", "call"
        if rbp and slot in ("tmp", "shadow", None) and region in CALL_TEMPS:
            return "pointer temps", "call " + region
        return "calls", region
    if region == "poll":
        return "polls", "poll"
    if region in ("chk", "lchk"):
        return "checks", region
    if slot == "lower":
        return "lowers", region.split("_")[0]
    if slot in ("thread", "aux"):
        return "calls", f"{slot} {region}"
    if rbp:
        pointer = region in POINTER_REGIONS or region.startswith("let_p_")
        kind = "phi" if region.startswith("phi_") else "let" if region.startswith("let_") else region
        return ("pointer temps" if pointer else "scalar temps"), kind
    if region == "jmp":
        return "selection", "jmp"
    if region == "br_test":
        return "selection", "jz" if op.startswith("j") else "test"
    if region.startswith("phi"):
        return "selection", "phi constant"
    if op.startswith("set") or (op == "movzbl" and "_cmp_" in region):
        return "selection", "boolean"
    if (op in ("movl", "movq", "movabsq") and args.startswith("$")) or (op == "xorl" and region.startswith("let")):
        return "selection", "constant"
    return "ops", "flight" if region == "flight" else region


def parse_s(path):
    """{line: ((category, subcategory), function, block)} of a marked .s."""
    out, region, slot, fn, block = {}, "prologue", None, "?", "?"
    for n, line in enumerate(open(path), 1):
        line = line.rstrip("\n")
        if m := REGION.match(line):
            region = m.group(1)
        elif m := SLOT.match(line):
            slot = m.group(1)
        elif (m := FUNC.match(line)) and not line.startswith(".L"):
            fn, region, block = m.group(1), "prologue", m.group(1)
        elif line.startswith(".L") and line.endswith(":") and not re.search(r"\.\.(jnz\.false|[jtf]\.poll)", line):
            block = line[:-1]
        elif (m := INS.match(line)) and not line.startswith("\t."):
            out[n] = (classify(region, slot, m.group(1), m.group(2), fn), fn, block, region, line)
            slot = None
    return out


def cg_lines(path):
    """{(file base name, line): Ir} and {function: Ir} of a cachegrind file."""
    lines, fns = collections.Counter(), collections.Counter()
    fl = fn = None
    for line in open(path):
        if line.startswith("fl="):
            fl = os.path.basename(line[3:].strip())
        elif line.startswith("fn="):
            fn = line[3:].strip()
        else:
            f = line.split()
            if len(f) == 2 and f[0].isdigit() and f[1].isdigit():
                lines[(fl, int(f[0]))] += int(f[1])
                fns[fn] += int(f[1])
    return lines, fns


def name(fn):
    m = re.match(r"pizlonated(?:FIP?\d+)?_(.*)", fn or "")
    return m.group(1) if m else fn


CATS = ["scalar temps", "pointer temps", "checks", "lowers", "calls", "polls", "selection", "ops", "runtime"]
rows, details = [], []
smaps = {}
for w, (prog, _, _) in W.items():
    if prog not in smaps:
        smaps[prog] = {os.path.basename(s): parse_s(s) for s in glob.glob(f"{M}/{prog}/s/*.s")}
    smap = smaps[prog]
    lines, _ = cg_lines(files[(w, "nf")])
    _, ref_fns = cg_lines(files[(w, "ref")])
    total = sum(lines.values())
    cat, sub, byfn = collections.Counter(), collections.Counter(), collections.Counter()
    blocks = collections.defaultdict(list)
    for (fl, ln), ir in lines.items():
        info = smap.get(fl, {}).get(ln)
        if info is None:
            cat["runtime"] += ir
            continue
        (c, s), fn, block, region, text = info
        cat[c] += ir
        sub[(c, s)] += ir
        byfn[fn] += ir
        blocks[(fl, block)].append((region, text, ir))
    # A block that only compares a value with a constant and branches: every
    # switch dispatch block, and the occasional `if`, so an upper bound.
    chain = 0
    for bl in blocks.values():
        regions = {re.sub(r"_\d+$", "", r) for r, _, _ in bl}
        texts = [t for _, t, _ in bl]
        materialized = any(re.match(r"\tset[a-z]+ ", t) for t in texts) and \
            any(re.match(r"\tmov[lq] \$-?\d+, %[re]cx", t) for t in texts)
        selected = any(re.match(r"\tcmp[lq] \$-?\d+, %", t) for t in texts)  # --branches=selected
        if regions <= {"let_w_cmp_cmp", "let_l_cmp_cmp", "br_test", "phi", "poll", "jmp"} and \
                (materialized or selected):
            chain += sum(ir for _, _, ir in bl)
    rows.append((w, sum(ref_fns.values()), total, cat, chain))
    details.append((w, sub, byfn, ref_fns, total))

G = 1e9
print("Billions of executed instructions, nanofil's share in parentheses.\n")
print("| Workload | filcc | nanofil | " + " | ".join(CATS) + " | const-compare blocks |")
print("|---|" + "--:|" * (len(CATS) + 3))
for w, ref, total, cat, chain in rows:
    pct = lambda x: f"{x / G:.2f} ({100 * x / total:.0f}%)"
    print(f"| {w} | {ref / G:.2f} | {total / G:.2f} | " + " | ".join(pct(cat[c]) for c in CATS) + f" | {pct(chain)} |")
for w, sub, byfn, ref_fns, total in details:
    print(f"\n{w}: subcategories over 1%")
    for (c, s), v in sub.most_common():
        if v > total / 100:
            print(f"  {c:14} {s:32} {v / G:7.3f}G {100 * v / total:5.1f}%")
    refn = collections.Counter()
    for f, v in ref_fns.items():
        refn[name(f)] += v
    print("  hottest functions, nanofil vs filcc (0: inlined by clang)")
    for f, v in byfn.most_common(6):
        print(f"  {name(f):40} {v / G:7.3f}G {refn[name(f)] / G:7.3f}G")

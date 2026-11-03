#!/usr/bin/env python3
"""Split nanofil -O's executed checks beyond filcc -O2's into causes
(docs/perf.md item 16), from checks.py's and checkclass.py's JSON.

usage: gap.py CHECKS.json CHECKCLASS.json

Prints two Markdown tables, in millions of executed checks. The first
gives the build ladder per workload: ref (filcc -O2), fwd (backward
propagation off), nosched (check optimization off), O (nanofil -O).
Its columns:

| column | meaning |
| --- | --- |
| trap | fwd - ref: what filcc removes only by moving a trap earlier |
| sched | nosched - fwd: filcc's forward scheduling over LLVM's IR |
| llvm | O - nosched: LLVM's IR before scheduling (GVN, LICM, inlining, registers) |
| inl | (ref-noinline - ref) - (O-noinline - O): inlining nanofil lacks |

The second table splits nanofil's own checks by checkclass's classes.
`cov` is a check or renewal that filcc's forward rule deletes
(covered, covered_hull, renew covered). `flg` needs only the flags
test. `part` is a root already checked at another range. `first` is a
root nothing covers, split by offset form.
"""
import json, sys

M = 1e6
ck, cc = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
W = list(cc)


def n(w, v, key="checks"):
    return ck.get(f"{w}|{v}", {}).get(key, 0) / M


print("| Workload | ref | fwd | nosched | O | O−ref | trap | sched | llvm | inl | O G / ref G |")
print("|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
tot = [0.0] * 9
for w in W:
    r, f, s, o = n(w, "ref"), n(w, "ref-fwd"), n(w, "ref-nosched"), n(w, "O")
    inl = (n(w, "ref-noinline") - r) - (n(w, "O-noinline") - o)
    g = n(w, "O", "ir_program") / max(n(w, "ref", "ir_program"), 1e-9)
    row = [r, f, s, o, o - r, f - r, s - f, o - s, inl]
    tot = [a + b for a, b in zip(tot, row)]
    print(f"| {w} | " + " | ".join(f"{x:.1f}" for x in row) + f" | {g:.2f} |")
print("| **all** | " + " | ".join(f"**{x:.0f}**" for x in tot) + " | |")

print()
print("Check instructions, millions; filcc's lower-only runs (ref / fwd / nosched) in the last column")
print()
print("| Workload | ref | fwd | nosched | O | O−ref | trap | sched | llvm | lower-only |")
print("|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
tot = [0.0] * 8
for w in W:
    r, f, s, o = (n(w, v, "check_ins") for v in ("ref", "ref-fwd", "ref-nosched", "O"))
    row = [r, f, s, o, o - r, f - r, s - f, o - s]
    tot = [a + b for a, b in zip(tot, row)]
    lo = " / ".join(f"{n(w, v, 'lower_only'):.0f}" for v in ("ref", "ref-fwd", "ref-nosched"))
    print(f"| {w} | " + " | ".join(f"{x:.0f}" for x in row) + f" | {lo} |")
print("| **all** | " + " | ".join(f"**{x:.0f}**" for x in tot) + " | |")

print()
print("Per function with inlining off on both sides, O-noinline minus")
print("ref-nosched-noinline, millions of checks:")
print()
for w in W:
    fa, fb = (ck.get(f"{w}|{v}", {}).get("functions", {}) for v in ("O-noinline", "ref-nosched-noinline"))
    d = {f: (fa.get(f, {}).get("checks", 0) - fb.get(f, {}).get("checks", 0)) / M for f in set(fa) | set(fb)}
    top = [f for f in sorted(d, key=lambda f: -abs(d[f]))[:6] if abs(d[f]) >= 0.5]
    print(f"- {w}: " + ", ".join(f"{f} {d[f]:+.1f}" for f in top))

print()
print("| Workload | O | cov | flg | part | first var | first base | first const | (in loops) | ins/check |")
print("|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
tot = [0.0] * 8
for w in W:
    s = dict.fromkeys(["cov", "flg", "part", "var", "base", "const", "loop"], 0.0)
    for k, v in cc[w]["classes"].items():
        op, cls, off, loop, _ = k.split("|")
        v /= M
        if op == "check_local":
            continue
        if cls in ("covered", "covered_hull"):
            s["cov"] += v
        elif cls in ("flags", "flags_hull"):
            s["flg"] += v
        elif cls.startswith("partial"):
            s["part"] += v
        else:
            s[off] += v
            if loop != "none":
                s["loop"] += v
    o = cc[w]["total"] / M
    ipc = n(w, "O", "check_ins") / max(n(w, "O"), 1e-9)
    row = [o] + [s[k] for k in ("cov", "flg", "part", "var", "base", "const", "loop")]
    tot = [a + b for a, b in zip(tot, row)]
    print(f"| {w} | " + " | ".join(f"{x:.1f}" for x in row) + f" | {ipc:.1f} |")
print("| **all** | " + " | ".join(f"**{x:.0f}**" for x in tot) + " | |")

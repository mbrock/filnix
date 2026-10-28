#!/usr/bin/env python3
"""Live-range splitting estimate (docs/perf.md 3d): how much of the scalar
frame traffic that the -O build leaves in a function's frame per-loop
registers could take, and what the edge moves would cost.

usage: split.py S_FILE FUNCTION CACHEGRIND_FILE...

S_FILE is a marked .s of the -O build (default.nix here) and the
cachegrind files come from profile.py's --work directory for the same
build. Scalar homes are found as coverage.py finds them, among the rbp
offsets the build still accesses. The registers 3a already uses are read
from the code: rbx, r12-r15, r10 and r11, live per instruction over the
function's CFG. Loops are natural loops of backward jumps. Each loop,
outermost first, gets the leftover homes it references, coloured by
their traffic inside it, in registers that no home occupies anywhere in
the loop (callee-saved ones if the home is live across a call in it).
An inner loop keeps its outer loop's homes. A home pays one move per
execution of each loop entry edge where it is live (a reload) and each
exit edge where it is live (a spill); it is kept only if its traffic in
the loop is larger. Edge counts are upper bounds: a conditional jump's
taken edge is min(executions of the jump, of its target).

It also prints the webs estimate: each home split into the connected
parts of its live range, coloured instead of whole homes (3a's rule,
whole moves only), with no moves. Approximate: homes by rbp offset,
whole-word liveness, noreturn calls not counted (perf.md 3d).
"""
import collections, os, re, sys

REGION = re.compile(r"^\.Lpf\.R\.([A-Za-z0-9_]+)\.\d+:$")
SLOT = re.compile(r"^\.Lpf\.S\.([A-Za-z0-9_]+)\.\d+:$")
LABEL = re.compile(r"^(\.?L[^\s:]*|[A-Za-z_][A-Za-z0-9_.$]*):$")
INS = re.compile(r"^\t([a-z][a-z0-9]*)\s*(.*)$")
RBP = re.compile(r"(-?\d+)\(%rbp\)")
NORETURN = re.compile(r"fail|failure|filc_cc_args_check")
CALLEE = ["rbx", "r12", "r13", "r14", "r15"]
SCRATCH = ["r10", "r11"]
ALLOC = CALLEE + SCRATCH
REGNAMES = {}
for r in ["rbx"]:
    for n in ["rbx", "ebx", "bx", "bl"]:
        REGNAMES[n] = r
for r in ["r10", "r11", "r12", "r13", "r14", "r15"]:
    for n in [r, r + "d", r + "w", r + "b"]:
        REGNAMES[n] = r
REGRE = re.compile(r"%(" + "|".join(sorted(REGNAMES, key=len, reverse=True)) + r")\b")

s_file, func, cgs = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(s_file).read().split("\n")
start = lines.index(f"{func}:")
end = next(i for i in range(start, len(lines)) if lines[i].startswith("\t.size"))
base = os.path.basename(s_file)
ir = collections.Counter()
for cg in cgs:
    fl = None
    for line in open(cg):
        if line.startswith("fl="):
            fl = os.path.basename(line[3:].strip())
        elif fl == base:
            f = line.split()
            if len(f) == 2 and f[0].isdigit():
                ir[int(f[0])] += int(f[1])

insns, labels = [], {}
region, slot = "prologue", None
for n in range(start + 1, end):
    line = lines[n]
    if m := REGION.match(line):
        region = m.group(1)
    elif m := SLOT.match(line):
        slot = m.group(1)
    elif m := LABEL.match(line):
        labels[m.group(1)] = len(insns)
    elif m := INS.match(line):
        insns.append((n + 1, m.group(1), m.group(2), region, slot))
        slot = None
N = len(insns)
cnt = [ir[ln] for ln, *_ in insns]


def operands(args):
    return [x.strip() for x in re.split(r",(?![^(]*\))", args)] if args else []


# Scalar homes, as coverage.py.
P_WRITERS = ("let_p_", "phi_p", "acc_raw_load_pointer_p")
weight, bad = collections.Counter(), set()
uses, defs = [set() for _ in insns], [set() for _ in insns]
for i, (ln, op, args, region, slot) in enumerate(insns):
    offs = [int(o) for o in RBP.findall(args)]
    if not offs:
        continue
    if op.startswith("lea"):
        bad.update(offs)
        continue
    if slot in ("lower", "thread", "aux"):
        bad.update(offs)
    ops = operands(args)
    dst = ops[-1] if ops else ""
    w = {int(m.group(1))} if (m := RBP.fullmatch(dst)) and not op.startswith(("cmp", "test")) else set()
    if w and (region.startswith(P_WRITERS) or region == "prologue"
              or (i + 1 < N and insns[i + 1][4] == "lower")):
        bad.update(w)
    for o in offs:
        weight[o] += cnt[i]
        here = f"{o}(%rbp)"
        if op.startswith("mov") and dst == here and here not in ops[0]:
            defs[i].add(o)
        elif dst == here and not op.startswith(("cmp", "test")):
            uses[i].add(o); defs[i].add(o)
        else:
            uses[i].add(o)
for i in range(N):
    uses[i] -= bad; defs[i] -= bad
homes = sorted(o for o in weight if o not in bad)
hidx = {o: k for k, o in enumerate(homes)}
total = sum(weight[o] for o in homes)

# Allocatable register uses and defs, by name (a write of a whole 32- or
# 64-bit destination by mov/movz/lea/set defines; anything else uses).
ruses, rdefs = [set() for _ in insns], [set() for _ in insns]
for i, (ln, op, args, _, _) in enumerate(insns):
    ops = operands(args)
    for k, o in enumerate(ops):
        for m in REGRE.finditer(o):
            r = REGNAMES[m.group(1)]
            whole = o == "%" + m.group(1) and not m.group(1).endswith(("w", "b", "bx", "bl"))
            if (k == len(ops) - 1 and whole and op.startswith(("mov", "lea", "set", "pop"))
                    and not op.startswith(("movb", "movw"))):
                rdefs[i].add(r)
            else:
                ruses[i].add(r)
    if op == "leave" or op == "ret":
        pass  # restores precede leave; they define, not use


def succ(i):
    ln, op, args, _, _ = insns[i]
    t = args.split()[0] if args else ""
    if op == "jmp":
        return [labels[t]] if t in labels else []
    if op.startswith("j"):
        return ([labels[t]] if t in labels else []) + [i + 1]
    if op in ("ret", "ud2"):
        return []
    return [i + 1] if i + 1 < N else []


S = [succ(i) for i in range(N)]
P = [[] for _ in range(N)]
for i in range(N):
    for j in S[i]:
        P[j].append(i)


def liveness(U, D):
    live_in = [0] * N
    changed = True
    while changed:
        changed = False
        for i in range(N - 1, -1, -1):
            out = 0
            for j in S[i]:
                out |= live_in[j]
            new = U[i] | (out & ~D[i])
            if new != live_in[i]:
                live_in[i] = new; changed = True
    return live_in


HU = [sum(1 << hidx[o] for o in uses[i]) for i in range(N)]
HD = [sum(1 << hidx[o] for o in defs[i] if o not in uses[i]) for i in range(N)]
hin = liveness(HU, HD)
ridx = {r: k for k, r in enumerate(ALLOC)}
RU = [sum(1 << ridx[r] for r in ruses[i]) for i in range(N)]
RD = [sum(1 << ridx[r] for r in rdefs[i] if r not in ruses[i]) for i in range(N)]
rin = liveness(RU, RD)


def out_of(live_in, i):
    o = 0
    for j in S[i]:
        o |= live_in[j]
    return o


hout = [out_of(hin, i) for i in range(N)]
rout = [out_of(rin, i) for i in range(N)]
calls = [i for i in range(N) if insns[i][1] == "call" and not NORETURN.search(insns[i][2])]

# Natural loops of backward jumps, merged by header.
bodies = collections.defaultdict(set)
for i in range(N):
    for h in S[i]:
        if h <= i:
            body, stack = {h}, [i]
            while stack:
                x = stack.pop()
                if x not in body:
                    body.add(x); stack.extend(P[x])
            bodies[h] |= body
loops = sorted(bodies.items(), key=lambda hb: -len(hb[1]))


def edge(p, t):
    """Upper bound on executions of the edge p -> t."""
    op = insns[p][1]
    if op.startswith("j") and op != "jmp":
        return min(cnt[p], cnt[t])
    return cnt[p]


def bits(x):
    k = 0
    while x:
        if x & 1:
            yield k
        x >>= 1; k += 1


loc = {}      # instruction -> {home: register}, from loops already done
gain = cost = 0
kept = []
for h, body in loops:
    occupied = 0
    for i in body:
        occupied |= rin[i] | rout[i] | RU[i] | sum(1 << ridx[r] for r in rdefs[i])
    taken_regs = {r for i in body for r in loc.get(i, {}).values()}
    w = collections.Counter()
    cross = set()
    for i in body:
        for o in uses[i] | defs[i]:
            if o not in loc.get(i, {}):
                w[o] += cnt[i]
    for i in calls:
        if i in body:
            for k in bits(hout[i]):
                cross.add(homes[k])
    adj = collections.defaultdict(set)
    for i in body:
        for o in defs[i]:
            for k in bits(hout[i]):
                if homes[k] != o:
                    adj[o].add(homes[k]); adj[homes[k]].add(o)
    entries = [(p, t) for t in body for p in P[t] if p not in body]
    exits = [(q, t) for q in body for t in S[q] if t not in body]
    colour = {}
    for o in sorted(w, key=lambda o: -w[o]):
        regs = CALLEE if o in cross else ALLOC
        busy = {colour[x] for x in adj[o] if x in colour}
        free = [r for r in regs if not (occupied >> ridx[r]) & 1 and r not in taken_regs and r not in busy]
        if not free:
            continue
        k = hidx[o]
        c = sum(edge(p, t) for p, t in entries if (hin[t] >> k) & 1)
        c += sum(edge(q, t) for q, t in exits if (hin[t] >> k) & 1)
        if w[o] > c:
            colour[o] = free[0]
            gain += w[o]; cost += c
            kept.append((h, o, free[0], w[o], c))
    for i in body:
        loc.setdefault(i, {}).update(colour)

fn = sum(cnt)
print(f"{func}: {N} insns, {fn/1e9:.3f}G Ir, leftover scalar home traffic {total/1e9:.3f}G "
      f"({100*total/max(fn,1):.1f}% of the function), {len(homes)} homes, {len(loops)} loops")
print(f"  split could take {gain/1e9:.3f}G ({100*gain/max(total,1):.0f}% of the leftover traffic) "
      f"for {cost/1e9:.3f}G of edge moves; net {100*(gain-cost)/max(fn,1):.1f}% of the function")
for h, o, r, wo, c in sorted(kept, key=lambda x: -x[3])[:12]:
    print(f"    loop@{insns[h][0]} home {o} -> {r}: {wo/1e6:.0f}M traffic, {c/1e6:.1f}M moves")

# Webs: each home's live ranges, split into connected parts (lines where
# it is live or accessed, joined along CFG edges it is live across). A
# web needs no moves: its home is dead wherever it meets another web.
parent = {}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def union(a, b):
    ra, rb = find(a), find(b)
    if ra != rb:
        parent[ra] = rb


webs = collections.defaultdict(list)   # (home, root) -> lines
for k, o in enumerate(homes):
    pts = [i for i in range(N) if (hin[i] >> k) & 1 or (hout[i] >> k) & 1 or o in uses[i] or o in defs[i]]
    for i in pts:
        parent[(k, i)] = (k, i)
    for i in pts:
        for j in S[i]:
            if (hin[j] >> k) & 1 and (k, j) in parent:
                union((k, i), (k, j))
    for i in pts:
        webs[(o, find((k, i)))].append(i)
# Accesses 3a can substitute: whole 32- or 64-bit moves, and widening
# loads, of exactly the home (amd64_regs_check:substitute/3). A home (3a)
# or a web (here) with any other access stays in its slot.
MOVES = ("movl", "movq", "movzbl", "movzbq", "movsbl", "movsbq", "movzwl", "movzwq",
         "movswl", "movswq", "movslq")
nonmove = [set() for _ in insns]
for i, (ln, op, args, _, _) in enumerate(insns):
    ops = operands(args)
    for k, o in enumerate(ops):
        m = RBP.fullmatch(o)
        if m and int(m.group(1)) in hidx:
            if op not in MOVES or len(ops) != 2 or (op not in ("movl", "movq") and k != 0):
                nonmove[i].add(int(m.group(1)))
callset = set(calls)


def colour(parts):
    """Greedy colouring of (home, lines) parts by traffic; returns the
    traffic of parts that get a register."""
    taken = collections.defaultdict(set)
    got = 0
    ws = []
    for o, pts in parts:
        acc = [i for i in pts if o in uses[i] or o in defs[i]]
        if any(o in nonmove[i] for i in acc):
            continue
        ws.append((sum(cnt[i] for i in acc), o, pts))
    for wt, o, pts in sorted(ws, key=lambda x: -x[0]):
        k = hidx[o]
        cross = any((hout[i] >> k) & 1 for i in pts if i in callset)
        occ = 0
        for i in pts:
            occ |= rin[i] | rout[i] | RU[i] | sum(1 << ridx[r] for r in rdefs[i])
        for r in (CALLEE if cross else ALLOC):
            if not (occ >> ridx[r]) & 1 and all(r not in taken[i] for i in pts):
                for i in pts:
                    taken[i].add(r)
                got += wt
                break
    return got


whole = collections.defaultdict(list)
for (o, r), pts in webs.items():
    whole[o].extend(pts)
hgain = colour(list(whole.items()))
wgain = colour([(o, pts) for (o, r), pts in webs.items()])
nweb = collections.Counter(o for o, _ in webs)
print(f"  3a rules (whole moves only), whole homes: {hgain/1e9:.3f}G ({100*hgain/max(total,1):.0f}%); "
      f"webs ({len(webs)}, median {sorted(nweb.values())[len(nweb)//2]} per home): "
      f"{wgain/1e9:.3f}G ({100*wgain/max(total,1):.0f}%), no moves")

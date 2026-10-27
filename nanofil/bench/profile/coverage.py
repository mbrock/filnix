#!/usr/bin/env python3
"""Item 3 coverage estimate: how much scalar frame traffic of a function
five callee-saved registers (rbx, r12-r15) plus r10/r11 (only for homes
live across no call) could hold, without splitting.

usage: coverage.py [--slow-paths-save] S_FILE FUNCTION CACHEGRIND_FILE...

S_FILE is a marked .s (default.nix here) and the cachegrind files come
from profile.py's --work directory for the same build. With
--slow-paths-save, runtime slow paths (poll, store barrier, ensure-aux)
are assumed to save r10/r11 themselves, so they do not count as calls.
Homes are rbp offsets. A home is eligible when no instruction touching it
is pointer or lower traffic and its address is never taken. Liveness is
per offset over the function's CFG; a home crosses a call when it is live
after a call that returns. Interference: live at the other's def.
Greedy colouring by dynamic weight (Ir of instructions touching the home).
"""
import collections, os, re, sys

REGION = re.compile(r"^\.Lpf\.R\.([A-Za-z0-9_]+)\.\d+:$")
SLOT = re.compile(r"^\.Lpf\.S\.([A-Za-z0-9_]+)\.\d+:$")
LABEL = re.compile(r"^(\.?L[^\s:]*|[A-Za-z_][A-Za-z0-9_.$]*):$")
INS = re.compile(r"^\t([a-z][a-z0-9]*)\s*(.*)$")
RBP = re.compile(r"(-?\d+)\(%rbp\)")
args = sys.argv[1:]
slow = "--slow-paths-save" in args
args = [x for x in args if x != "--slow-paths-save"]
# Calls that do not return, or (with --slow-paths-save) that are cold.
NORETURN = re.compile(r"fail|failure|filc_cc_args_check" + (r"|pollcheck_slow|_slow@|ensure_aux_ptr_outline" if slow else ""))

s_file, func, cgs = args[0], args[1], args[2:]
lines = open(s_file).read().split("\n")
start = lines.index(f"{func}:")
end = next(i for i in range(start, len(lines)) if lines[i].startswith("\t.size"))

# Ir per line, summed over the cachegrind files given.
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

# Instructions: (line number, op, args, region, slot).
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
    elif (m := INS.match(line)):
        insns.append((n + 1, m.group(1), m.group(2), region, slot))
        slot = None

def written(i):
    """The rbp offsets instruction i stores to."""
    ln, op, args, region, slot = insns[i]
    ops = [x.strip() for x in re.split(r",(?![^(]*\))", args)]
    m = RBP.fullmatch(ops[-1]) if ops else None
    return {int(m.group(1))} if m and not op.startswith(("cmp", "test")) else set()

# Pointer material: lower/thread/aux slots, anything stored in a region
# that produces a pointer, a payload store followed by its lower's store,
# and addressed slots. Reads in pointer regions (indexes, offsets) do not
# taint a slot.
P_WRITERS = ("let_p_", "phi_p", "acc_raw_load_pointer_p")

# Slot facts.
weight, bad, total_scalar = collections.Counter(), set(), 0
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
    w = written(i)
    if w and (region.startswith(P_WRITERS) or region == "prologue"
              or (i + 1 < len(insns) and insns[i + 1][4] == "lower")):
        bad.update(w)
    for o in offs:
        weight[o] += ir[ln]
    ops = [x.strip() for x in re.split(r",(?![^(]*\))", args)]
    dst = ops[-1]
    for o in offs:
        here = f"{o}(%rbp)"
        if op.startswith("mov") and dst == here and here not in ops[0]:
            defs[i].add(o)
        elif dst == here and op.startswith(("cmp", "test")):
            uses[i].add(o)
        elif dst == here:
            uses[i].add(o); defs[i].add(o)
        else:
            uses[i].add(o)
# Pointer slots are excluded everywhere: drop them from the sets.
for i in range(len(insns)):
    uses[i] -= bad; defs[i] -= bad
scalar_w = {o: w for o, w in weight.items() if o not in bad}
total_scalar = sum(scalar_w.values())

# CFG successors per instruction.
def succ(i):
    ln, op, args, _, _ = insns[i]
    t = args.split()[0] if args else ""
    if op == "jmp":
        return [labels[t]] if t in labels else []
    if op.startswith("j"):
        return ([labels[t]] if t in labels else []) + [i + 1]
    if op in ("ret", "ud2"):
        return []
    return [i + 1] if i + 1 < len(insns) else []
S = [succ(i) for i in range(len(insns))]
unknown = [insns[i] for i in range(len(insns)) if insns[i][1] == "jmp" and not S[i] and not insns[i][2].startswith("*") and "@PLT" not in insns[i][2]]

# Bitset liveness, iterated to a fixed point over instructions.
idx = {o: k for k, o in enumerate(sorted(scalar_w))}
U = [sum(1 << idx[o] for o in uses[i]) for i in range(len(insns))]
D = [sum(1 << idx[o] for o in defs[i] if o not in uses[i]) for i in range(len(insns))]
live_in = [0] * len(insns)
changed = True
while changed:
    changed = False
    for i in range(len(insns) - 1, -1, -1):
        out = 0
        for j in S[i]:
            out |= live_in[j]
        new = U[i] | (out & ~D[i])
        if new != live_in[i]:
            live_in[i] = new; changed = True

def bits(x):
    k = 0
    while x:
        if x & 1:
            yield k
        x >>= 1; k += 1

rev = {k: o for o, k in idx.items()}
cross = 0
adj = collections.defaultdict(int)
for i, (ln, op, args, region, slot) in enumerate(insns):
    out = 0
    for j in S[i]:
        out |= live_in[j]
    if op == "call" and not NORETURN.search(args):
        cross |= out
    for o in defs[i]:
        k = idx[o]
        others = out & ~(1 << k)
        adj[k] |= others
        for m in bits(others):
            adj[m] |= 1 << k

CALLEE = ["rbx", "r12", "r13", "r14", "r15"]
SCRATCH = ["r10", "r11"]
colour = {}
for o in sorted(scalar_w, key=lambda o: -scalar_w[o]):
    k = idx[o]
    regs = CALLEE if (cross >> k) & 1 else CALLEE + SCRATCH
    taken = {colour[m] for m in bits(adj[k]) if m in colour}
    free = [r for r in regs if r not in taken]
    if free:
        colour[k] = free[0]

covered = sum(scalar_w[rev[k]] for k in colour)
crossw = sum(scalar_w[rev[k]] for k in bits(cross))
fn_ir = sum(ir[ln] for ln, *_ in insns)
print(f"{func}: {len(insns)} insns, {fn_ir/1e9:.3f}G Ir, scalar home traffic {total_scalar/1e9:.3f}G "
      f"({100*total_scalar/max(fn_ir,1):.0f}% of the function), {len(scalar_w)} scalar homes, {len(bad)} pointer/addressed")
print(f"  live across a call: {100*crossw/max(total_scalar,1):.0f}% of the traffic")
print(f"  covered by 5 callee-saved + r10/r11: {100*covered/max(total_scalar,1):.0f}% ({len(colour)} homes)")
top = sorted(scalar_w.items(), key=lambda x: -x[1])[:12]
print("  hottest homes: " + ", ".join(f"{o}:{w/1e6:.0f}M{'*' if (cross>>idx[o])&1 else ''}{'='+colour[idx[o]] if idx[o] in colour else ''}" for o, w in top))
if unknown:
    print(f"  unresolved jumps: {len(unknown)}")

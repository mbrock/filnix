#!/usr/bin/env python3
"""Count executed access checks per workload and function (docs/perf.md
item 16), for filcc and nanofil builds alike.

Runs every gate workload under callgrind (--dump-instr=yes) with every
build variant of checks.nix, then reads each binary's disassembly. A
*fail block* is a jump target that reaches a call to
filc_optimized_access_check_fail within a few instructions without
branching; both compilers' checks branch to one. A *test* is an executed
conditional jump to a fail block, classified by the instruction that set
its flags:

| kind  | flag setter |
| ---   | --- |
| null  | `test %r, %r` (the lower is null) |
| lower | `cmp` of the pointer with the lower |
| upper | `cmp` with a register loaded from `-0x10(lower)` (upper), or that load itself |
| flags | `test`/`and` of the object's flags (`-0x2(lower)` or `-0x8(lower)` with a mask): free, read-only |
| align | `test $imm, %reg` |

A *check* is one run of tests with nothing but check instructions
between them (tests, compares, the header loads, constant masks and the
upper's adjustment): one scheduled check of filcc, one full check or
renewal of nanofil. Its kind is the set of its tests' kinds. Check
instructions are the instructions of those runs, from the first test's
flag setter (and the header loads just before it) to the last test.

Valgrind attributes by address, so inlined code counts in its caller.
nanofil's builds keep their block labels as symbols (`as -L`), so its
counts are also given per block.

usage: checks.py [--builds DIR] [--bench DIR] [--work DIR] [--only SUBSTR]
                 [--variants a,b] [--top N] [--json FILE]
Needs valgrind on PATH or in $VALGRIND, and objdump.
"""
import argparse, collections, json, os, re, subprocess
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("--builds", default=f"{HERE}/checks")
ap.add_argument("--bench", default=f"{HERE}/../out", help="the gate's build, for its inputs")
ap.add_argument("--work", default="checks-work")
ap.add_argument("--only", default="")
ap.add_argument("--variants", default="ref,ref-noinline,ref-fwd,ref-fwd-noinline,ref-nosched,O,O-noinline")
ap.add_argument("--top", type=int, default=12, help="functions per workload in the tables")
ap.add_argument("--json", default="checks.json")
ap.add_argument("--dump", metavar="FUNCTION",
                help="print FUNCTION's executed instructions with counts, check runs and test kinds, and exit")
a = ap.parse_args()
os.makedirs(a.work, exist_ok=True)
D, L = a.builds, os.path.dirname(HERE)
TEXT, RANDOM = f"{a.bench}/inputs/text", f"{a.bench}/inputs/random"
EXE = {"zlib": "minigzip", "bzip2": "bzip2", "lz4": "lz4", "lua": "lua", "sqlite": "sqlite3"}
VARIANTS = [v for v in a.variants.split(",") if v]


def ref_output(prog, args, src, name):
    path = f"{a.work}/{name}"
    if not os.path.exists(path):
        with open(src, "rb") as i, open(path, "wb") as o:
            subprocess.run([f"{D}/{prog}/ref/{EXE[prog]}", *args], stdin=i, stdout=o, check=True)
    return path


W = {
    "zlib -6": ("zlib", ["-6"], TEXT),
    "zlib -d": ("zlib", ["-d"], lambda: ref_output("zlib", ["-6"], TEXT, "text.gz")),
    "bzip2 -9": ("bzip2", ["-9"], TEXT),
    "bzip2 -d": ("bzip2", ["-d"], lambda: ref_output("bzip2", ["-9"], TEXT, "text.bz2")),
    "lz4 -1": ("lz4", ["-q", "-1"], RANDOM),
    "lz4 -9": ("lz4", ["-q", "-9"], TEXT),
    "lz4 -d": ("lz4", ["-q", "-d"], lambda: ref_output("lz4", ["-q", "-9"], TEXT, "text.lz4")),
    "lua int": ("lua", [f"{L}/int.lua"], None),
    "lua tab": ("lua", [f"{L}/tab.lua"], None),
    "lua str": ("lua", [f"{L}/str.lua"], None),
    "sqlite": ("sqlite", [], f"{L}/sqlite.sql"),
}
W = {k: v for k, v in W.items() if a.only in k}
key = lambda w: re.sub(r"\W+", "-", w)


def callgrind(w, variant):
    prog, args, stdin = W[w]
    stdin = stdin() if callable(stdin) else stdin
    out = f"{a.work}/cg.{variant}.{key(w)}"
    # The store path of the binary, so a later rebuild (filcc's output
    # differs from build to build) cannot be paired with these counts.
    exe = os.path.realpath(f"{D}/{prog}/{variant}/{EXE[prog]}")
    if os.path.exists(out) and exe_of(out) != exe:
        os.remove(out)
    if not os.path.exists(out):
        # --aspace-minaddr: Fil-C's ioctl wrapper asserts that an integer
        # argument below 4 GiB is not a heap pointer (profile.py).
        cmd = [os.environ.get("VALGRIND", "valgrind"), "--aspace-minaddr=0x100000000", "--tool=callgrind",
               "--dump-instr=yes", "--compress-pos=no", "--compress-strings=no",
               f"--callgrind-out-file={out}.tmp", exe, *args]
        with open(stdin or os.devnull, "rb") as i:
            subprocess.run(cmd, stdin=i, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        os.rename(f"{out}.tmp", out)
    return out


def exe_of(path):
    """The binary a callgrind file ran."""
    for line in open(path):
        if line.startswith("cmd:"):
            return line.split()[1]
    return None


def executed(path, exe):
    """{address: Ir} of the instructions of `exe` in a callgrind file."""
    ir, skip, ob = collections.Counter(), False, None
    exe = os.path.realpath(exe)
    for line in open(path):
        if line.startswith("ob="):
            ob = os.path.realpath(line[3:].strip())
            continue
        if line.startswith("calls="):
            skip = True  # the next line is the call's inclusive cost
            continue
        f = line.split()
        if len(f) == 3 and f[0].startswith("0x") and not skip and ob == exe:
            ir[int(f[0], 16)] += int(f[2])
        skip = False
    return ir


INS = re.compile(r"^\s+([0-9a-f]+):\s+(\S+)\s*(.*?)\s*$")
SYM = re.compile(r"^([0-9a-f]+) <(.*)>:$")
TARGET = re.compile(r"^([0-9a-f]+) <")
HEADER = re.compile(r"-0x(10|8|2)\(%r(?!bp|sp)[a-z0-9]+\)")
HEADER_BASE = re.compile(r"-0x(?:10|8|2)\(%(r(?!bp|sp)[a-z0-9]+)\)")
UPPER_LOAD = re.compile(r"^-0x10\(%r(?!bp|sp)[a-z0-9]+\),(%\w+)$")
REG = re.compile(r"^%\w+$")
AUX_MASK = (1 << 48) - 1


def operands(args):
    """Split AT&T operands at top-level commas."""
    out, depth, cur = [], 0, ""
    for c in args.split("#")[0].split("<")[0].strip():
        if c == "," and depth == 0:
            out.append(cur.strip()); cur = ""
            continue
        depth += c == "("; depth -= c == ")"
        cur += c
    return out + [cur.strip()] if cur.strip() else out


def reg64(r):
    """The 64-bit register of a register operand, so %eax and %rax compare equal."""
    r = r.lstrip("%")
    if m := re.fullmatch(r"r(\d+)[dwb]?", r):
        return "r" + m.group(1)
    for base in ("ax", "bx", "cx", "dx"):
        if r in ("r" + base, "e" + base, base, base[0] + "l", base[0] + "h"):
            return "r" + base
    for base in ("si", "di", "bp", "sp"):
        if r in ("r" + base, "e" + base, base, base + "l"):
            return "r" + base
    return r


def analyse(exe):
    """Per address: (function, block, check id or None, test kind or None, is check instruction);
    per check id the set of its tests' kinds; per check id the address of its first test."""
    dis = subprocess.run(["objdump", "-d", "--no-show-raw-insn", "-M", "att", exe],
                         capture_output=True, text=True, check=True).stdout
    insns, fn, block = [], "?", "?"
    for line in dis.splitlines():
        if m := SYM.match(line):
            name = m.group(2)
            if name.startswith(".L"):
                block = name
            else:
                fn = block = name
        elif m := INS.match(line):
            if m.group(2) != "(bad)":
                insns.append((int(m.group(1), 16), m.group(2), m.group(3), fn, block))
    index = {ins[0]: i for i, ins in enumerate(insns)}

    def is_fail(addr):
        """(kind, pointer register, lower register) when addr starts a fail
        block, else False. The block passes the pointer in %rdi and the lower
        in %rsi; a register the block does not set is passed as it is.
        Straight on, or through direct jumps (LLVM shares the call between
        fail blocks that differ only in their origin)."""
        i, budget, args_of = index.get(addr), 16, {}
        while i is not None and budget:
            _, op, args, _, _ = insns[i]
            if op.startswith("call"):
                kind = "heap" if "filc_optimized_access_check_fail" in args else \
                    "local" if "filc_optimized_stack_access_check_fail" in args else None
                if kind is None:
                    return False
                return (kind, args_of.get("rdi", "rdi"), args_of.get("rsi", "rsi"))
            if op in ("jmp", "jmpq") and (m := TARGET.match(args)):
                i = index.get(int(m.group(1), 16))
            elif op.startswith("j") or op.startswith("ret") or op == "ud2":
                return False
            else:
                ops = operands(args)
                if len(ops) == 2 and REG.match(ops[1]) and reg64(ops[1]) in ("rdi", "rsi") \
                        and reg64(ops[1]) not in args_of:
                    args_of[reg64(ops[1])] = reg64(ops[0]) if op.startswith("mov") and REG.match(ops[0]) else None
                i += 1
            budget -= 1
        return False

    fail = {}

    def test_target(i, op, args):
        # A conditional jump to a fail block, or one that falls through into
        # one (LLVM sometimes inverts a check to jump to the access).
        if op.startswith("j") and op not in ("jmp", "jmpq") and (m := TARGET.match(args)):
            for t in (int(m.group(1), 16), insns[i + 1][0] if i + 1 < len(insns) else None):
                if t is None:
                    continue
                if t not in fail:
                    fail[t] = is_fail(t)
                if fail[t]:
                    return fail[t]
        return False

    regs = lambda s: {reg64(r) for r in re.findall(r"%\w+", s)}
    info, kinds, first, members, last = {}, {}, {}, collections.defaultdict(list), {}
    upper, header, masks, prev_fn, run, cid = set(), set(), {}, None, None, 0
    lowers, run_ptr, ptr_redefined = set(), None, False
    for i, (addr, op, args, fn, block) in enumerate(insns):
        if fn != prev_fn:
            upper, header, masks, run, prev_fn = set(), set(), {}, None, fn
            lowers, run_ptr, ptr_redefined = set(), None, False
        info[addr] = (fn, block, None, None, False)
        ops = operands(args)
        writes = not op.startswith(("cmp", "test", "bt", "j", "push", "call", "nop"))
        dest = reg64(ops[-1]) if writes and ops and REG.match(ops[-1]) else None
        src = ops[0] if ops else ""
        is_test = test_target(i, op, args)
        # Check instructions: what a check is made of. Neutral ones (register
        # moves and arithmetic) neither start nor end a run.
        checkish = is_test or op.startswith(("test", "cmp", "and", "movabs")) or \
            (op.startswith("mov") and bool(HEADER.search(args))) or \
            (op.startswith(("add", "sub")) and dest in upper)
        neutral = (op.startswith(("mov", "lea", "add", "sub")) and len(ops) == 2 and
                   all(REG.match(o) or o.startswith("$") for o in ops)) or op.startswith("lea")
        if is_test:
            fkind, fptr, flower = is_test
            is_test = fkind
        if is_test == "local":
            # nanofil's check of a local's exact bounds (filc_amd64.pl's
            # local_check), counted apart: it reads no object header.
            kind = "local"
        if is_test:
            sop, sargs = insns[i - 1][1], insns[i - 1][2]
            sops = operands(sargs)
            touches_header = bool(HEADER.search(sargs)) or bool(regs(sargs) & header)
            mask = max((masks.get(r, 0) for r in regs(sargs)), default=0)
            if is_test == "local":
                pass
            elif sop.startswith("test") and len(sops) == 2 and sops[0] == sops[1] and REG.match(sops[0]):
                kind = "null"
            elif sop.startswith(("test", "and")) and mask:
                kind = "null" if mask == AUX_MASK else "flags"
            elif sop.startswith(("test", "and")) and touches_header:
                # A zero aux word means the loaded pointer is null: the jump is
                # its null test, threaded through the aux load.
                kind = "null" if op in ("je", "jz") else "flags"
            elif sop.startswith(("test", "and")):
                kind = "align"
            elif sop.startswith("cmp"):
                # The fail block names the pointer and the lower: a compare
                # with the lower is the lower test, any other compare of
                # the pointer the upper test.
                rs = {reg64(r) for r in re.findall(r"%\w+", sargs) if not re.search(r"\(%" + r[1:], sargs)}
                if "-0x10(" in sargs:
                    kind = "upper"
                elif flower in rs and fptr in rs:
                    kind = "lower"
                else:
                    # Otherwise by direction: the test fails when the
                    # pointer is below the bound (lower) or above it
                    # (upper). This holds when LLVM hoisted the upper into
                    # a stack slot, so no -0x10(lower) load is in sight.
                    x, y = (sops + ["", ""])[:2]
                    rx, ry = (reg64(o) if REG.match(o) else None for o in (x, y))
                    if fptr and fptr == rx:
                        ptr_is_y = False
                    elif fptr and fptr == ry:
                        ptr_is_y = True
                    elif rx and ry and (ry in lowers or ry in upper) and rx not in lowers | upper:
                        ptr_is_y = False
                    else:
                        ptr_is_y = True
                    m = TARGET.match(args)
                    to_fail = bool(m and fail.get(int(m.group(1), 16)))
                    # cmp X, Y sets flags of Y - X; "below" jumps when Y < X.
                    below = op in ("jb", "jnae", "jc", "jbe", "jna", "jl", "jnge", "jle", "jng")
                    ptr_below = below if ptr_is_y else not below
                    kind = "lower" if ptr_below == to_fail else "upper"
            elif sop.startswith("sub") and len(sops) == 2 and all(REG.match(o) for o in sops):
                kind = "lower"  # ptr - lower borrows
            else:
                kind = "other"
            # The pointer a bounds test compares: the register operand that
            # is neither a lower nor an upper. A second pointer in one run
            # is a second check whose null test and upper load LLVM shared
            # with the first (mainGtU's block[i1], block[i2]).
            ptr = fptr if kind in ("lower", "upper") and is_test == "heap" else None
            if ptr is None and kind in ("lower", "upper") and sop.startswith(("cmp", "sub")):
                cands = [reg64(o) for o in sops if REG.match(o)]
                cands = [r for r in cands if r not in lowers and r not in upper]
                ptr = cands[-1] if cands else None
            if run is not None and ptr is not None and run_ptr is not None and \
                    (ptr != run_ptr or ptr_redefined):
                run = None
            if run is None:
                cid += 1
                run = cid
                kinds[run], first[run] = set(), addr
                run_ptr, ptr_redefined = None, False
            if ptr is not None and run_ptr is None:
                run_ptr = ptr
                # The flag setter and header loads just before the first test.
                k = i - 1
                while k >= 0 and insns[k][3] == fn and info[insns[k][0]][2] is None and (
                        insns[k][1].startswith(("test", "cmp", "and", "movabs", "sub")) or
                        (insns[k][1].startswith("mov") and HEADER.search(insns[k][2]))):
                    members[run].insert(0, insns[k][0])
                    k -= 1
            kinds[run].add(kind)
            members[run].append(addr)
            last[run] = addr
            info[addr] = (fn, block, run, kind, False)
        elif checkish or neutral:
            if run is not None:
                members[run].append(addr)
        else:
            run = None
        if dest and dest == run_ptr:
            ptr_redefined = True
        # Lowers: registers whose header is read or that are null-tested.
        for m in HEADER_BASE.finditer(args):
            lowers.add(reg64(m.group(1)))
        if is_test and kind == "null" and sop.startswith("test") and REG.match(sops[0]):
            lowers.add(reg64(sops[0]))
        # Taint after the instruction: uppers, header words, and the masks
        # of the aux pointer (low 48 bits) or the flags (bits 48 and up).
        if dest:
            masks.pop(dest, None)
        if op == "movabs" and src.startswith("$") and dest and (int(src[1:], 0) == AUX_MASK or int(src[1:], 0) >> 48):
            masks[dest] = int(src[1:], 0)
        if op.startswith("mov") and (m := UPPER_LOAD.match(args)):
            upper.add(reg64(m.group(1)))
        elif op.startswith("mov") and HEADER.search(src) and dest:
            header.add(dest); upper.discard(dest)
        elif op.startswith("lea") and dest and re.fullmatch(r"-?(0x[0-9a-f]+)?\(%\w+\)", src) and regs(src) & upper:
            upper.add(dest)  # upper - Size as a lea
        elif op.startswith(("add", "sub")) and dest in upper:
            pass  # upper - Size
        elif op.startswith("and") and dest and regs(args) & header:
            header.add(dest)
        elif op.startswith("mov") and dest and REG.match(src) and reg64(src) in upper:
            upper.add(dest)
        elif dest and not op.startswith(("cmp", "test")):
            upper.discard(dest); header.discard(dest)
        if dest and not op.startswith(("cmp", "test")) and not HEADER_BASE.search(args):
            lowers.discard(dest)
        if op.startswith("mov") and dest and REG.match(src) and reg64(src) in lowers:
            lowers.add(dest)
    for run, addrs in members.items():
        for x in addrs:
            if x > last[run]:
                break
            f, b, r, k, _ = info[x]
            info[x] = (f, b, run, k, True)
    # Accesses: executed instructions that read or write memory other than
    # the frame, the stack, globals by rip, or an object's header.
    access = set()
    for addr, op, args, fn, block in insns:
        if info[addr][4] or op.startswith(("lea", "nop", "call", "jmp", "prefetch")) or op.startswith("j"):
            continue
        mem = re.search(r"-?(0x[0-9a-f]+)?\(%(\w+)(,%\w+)?(,\d)?\)", args)
        if mem and mem.group(2) not in ("rbp", "rsp", "rip") and not HEADER.search(args):
            access.add(addr)
    return info, kinds, first, access


def name(fn):
    m = re.match(r"pizlonated(?:FIP?\d+)?_(.*)", fn or "")
    return m.group(1) if m else fn


def by_name(fns):
    """Per function name: the totals of its symbols (a function's body and
    its entry thunk both reduce to its C name)."""
    out = {}
    for f, d in fns.items():
        if not d["ir"]:
            continue
        o = out.setdefault(name(f), {"ir": 0, "checks": 0, "local": 0, "lower_only": 0, "check_ins": 0, "accesses": 0,
                                     "tests": collections.Counter(), "shapes": collections.Counter()})
        for k in ("ir", "checks", "local", "lower_only", "check_ins", "accesses"):
            o[k] += d[k]
        o["tests"] += d["tests"]
        o["shapes"] += d["shapes"]
    return {f: dict(o, tests=dict(o["tests"]), shapes=dict(o["shapes"])) for f, o in out.items()}


def tally(info, kinds, first, access, ir):
    """Per function and per block: Ir, checks by kind set, tests by kind, check instructions."""
    z = lambda: {"ir": 0, "checks": 0, "local": 0, "lower_only": 0, "check_ins": 0, "accesses": 0, "tests": collections.Counter(), "shapes": collections.Counter()}
    fns, blocks = collections.defaultdict(z), collections.defaultdict(z)
    for addr, n in ir.items():
        if addr not in info:
            continue
        fn, block, run, kind, ins = info[addr]
        for d in (fns[fn], blocks[(fn, block)]):
            d["ir"] += n
            if ins:
                d["check_ins"] += n
            if addr in access:
                d["accesses"] += n
            if kind:
                d["tests"][kind] += n
            # A check is an upper test, or a run of tests with no bounds
            # test (a renewal, filcc's not-freed check). A run with a lower
            # test but no upper is a partial check, or the lower half of a
            # check whose branch LLVM inverted at a loop's latch, so it
            # counts apart (lower_only) rather than twice.
            if kind == "upper" and run is not None and "local" not in kinds[run]:
                d["checks"] += n
            if run is not None and first.get(run) == addr:
                if "local" in kinds[run]:
                    d["local"] += n
                elif "upper" not in kinds[run] and "lower" not in kinds[run]:
                    d["checks"] += n
                elif "upper" not in kinds[run]:
                    d["lower_only"] += n
                d["shapes"]["+".join(sorted(kinds[run]))] += n
    return fns, blocks


runs = {(w, v): None for w in W for v in VARIANTS}
with ThreadPoolExecutor(max_workers=max(1, (os.cpu_count() or 2) // 2)) as ex:
    futs = {k: ex.submit(callgrind, *k) for k in runs}
    files = {k: f.result() for k, f in futs.items()}

analyses = {}
results = {}
for (w, v), path in files.items():
    exe = exe_of(path)
    if exe not in analyses:
        analyses[exe] = analyse(exe)
    info, kinds, first, access = analyses[exe]
    ir = executed(path, exe)
    if a.dump:
        dis = subprocess.run(["objdump", "-d", "--no-show-raw-insn", "-M", "att", exe],
                             capture_output=True, text=True, check=True).stdout
        print(f"== {w} {v}")
        on = False
        for line in dis.splitlines():
            if m := SYM.match(line):
                if not m.group(2).startswith(".L"):
                    on = name(m.group(2)) == a.dump
                if on:
                    print(line)
            elif on and (m := INS.match(line)):
                addr = int(m.group(1), 16)
                fn, block, run, kind, ins = info.get(addr, (0, 0, None, None, False))
                n = ir.get(addr, 0)
                tag = f"c{run}{'*' if first.get(run) == addr else ''} {kind or ''}" if ins else ""
                print(f"{n / 1e6:10.2f}M {tag:14} {m.group(2):8} {m.group(3)}")
        continue
    fns, blocks = tally(info, kinds, first, access, ir)
    total = sum(d["ir"] for d in fns.values())
    piz = {f: d for f, d in fns.items() if f.startswith("pizlonated")}
    results[(w, v)] = {
        "ir_program": total,
        "checks": sum(d["checks"] for d in piz.values()),
        "local": sum(d["local"] for d in piz.values()),
        "lower_only": sum(d["lower_only"] for d in piz.values()),
        "accesses": sum(d["accesses"] for d in piz.values()),
        "check_ins": sum(d["check_ins"] for d in piz.values()),
        "tests": dict(sum((d["tests"] for d in piz.values()), collections.Counter())),
        "shapes": dict(sum((d["shapes"] for d in piz.values()), collections.Counter())),
        "functions": by_name(piz),
        "blocks": {f"{name(f)} {b}": {"ir": d["ir"], "checks": d["checks"], "check_ins": d["check_ins"],
                                      "tests": dict(d["tests"])}
                   for (f, b), d in blocks.items() if d["checks"] and f != b},
    }

if a.dump:
    raise SystemExit
json.dump({f"{w}|{v}": r for (w, v), r in results.items()}, open(a.json, "w"))
M = 1e6
print("Executed checks, millions (check instructions, millions; instructions in the program's own code, G).")
print("Lower-only runs and nanofil's local checks are not in the count.\n")
print("| Workload | " + " | ".join(VARIANTS) + " |\n|---|" + "--:|" * len(VARIANTS))
for w in W:
    cells = []
    for v in VARIANTS:
        r = results[(w, v)]
        cells.append(f"{r['checks'] / M:.1f} ({r['check_ins'] / M:.0f}; {r['ir_program'] / 1e9:.2f}G)")
    print(f"| {w} | " + " | ".join(cells) + " |")
print("\nTests by kind, millions\n")
kinds_all = ["null", "lower", "upper", "flags", "align", "other"]
for w in W:
    print(f"{w}: " + "; ".join(f"{v} " + " ".join(f"{k} {results[(w, v)]['tests'].get(k, 0) / M:.1f}"
                                                   for k in kinds_all) for v in VARIANTS))
for w in W:
    print(f"\n{w}: hottest functions by checks, millions (" + ", ".join(VARIANTS) + ")")
    agg = collections.Counter()
    for v in VARIANTS:
        for f, d in results[(w, v)]["functions"].items():
            agg[f] = max(agg[f], d["checks"])
    for f, _ in agg.most_common(a.top):
        print(f"  {f:36} " + " ".join(f"{results[(w, v)]['functions'].get(f, {}).get('checks', 0) / M:8.1f}"
                                      for v in VARIANTS))

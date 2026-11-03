#!/usr/bin/env python3
"""Prove the shortened bounds checks of shared check parts
(check_share.pl, docs/perf.md item 17) equivalent to Fil-C's condition,
with Z3 over 64-bit bit-vectors. The sibling of tests/bounds_smt.py.

The lines come from the compiler itself, through bin/nanofil --script:
check_share:share_bounds//4 for each check, and check_share:shared_uppers/2
over the stream, which turns a reused upper into its adjustment, so the
proof is about what nanofil emits. They are interpreted here with x86-64
semantics for the few instructions they use.

Three cases, for every access size (and producer size) and register:

1. full: share_bounds(test, load(R), Size): the check as the reference
   emits it, R being %rdx or %r9;
2. known: share_bounds(known, load(R), Size), without the null test;
3. reuse: a full check of Size0 bytes at ptr0, then a reload of %rax, then
   share_bounds(Null, reuse(r9), Size) at ptr, for Size0, Size =< 16,
   resolved by shared_uppers/2. The second check runs only when the first
   passed.

Each must pass exactly when

    lower != 0  and  lower =< ptr  and  ptr + Size =< upper

(ptr + Size in unbounded integers), and never read a null lower's header,
under these assumptions about the reused values:

- for a nonnull lower, what Fil-C's runtime guarantees (as bounds_smt.py):
  16 =< lower =< upper < 2^Bits, Bits = 47 and 56 checked separately;
- known: lower != 0. A passed check of a pointer with the same lower root
  dominates this one (ir.pl's lower_chain/3: every name on the way has one
  definition, so the lower is the same value);
- reuse: %rcx holds the same lower in both checks (the same root), the
  object's upper is the same at both (nothing between can free it: the
  invalidators of check_share.pl; a free racing from another thread is
  outside this model, as for every check), and %r9 is unchanged between
  them (shared_uppers/2 keeps the fact only across lines that do not
  write it).

A control drops the unchanged-upper assumption (the object freed between
the checks, upper = lower at the second): reuse must then be refuted,
showing that the assumption is what the proof rests on.

Run from nanofil/:  python3 tests/share_smt.py   (needs z3-solver)
"""
import os
import subprocess
import sys
import tempfile

import z3

SIZES = [1, 2, 4, 8, 10, 16]
FULL_SIZES = SIZES + [17, 32, 4096, 2147483647]

GOAL = r"""
:- use_module('%s').
print_lines(Is) :-
    forall(member(ins(Op, W, Os), Is),
           ( format("ins ~w ~w", [Op, W]),
             forall(member(O, Os),
                    ( O = reg(R) -> format(" reg:~w", [R])
                    ; O = imm(N) -> format(" imm:~w", [N])
                    ; O = mem(D, B) -> format(" mem:~w:~w", [D, B])
                    ; O = sym(S) -> format(" sym:~w", [S]) )),
             nl )).
one(Null, Upper, Size) :-
    phrase(check_share:share_bounds(Null, Upper, Size, fail), Ls0),
    check_share:shared_uppers(Ls0, Ls), print_lines(Ls).
:- initialization((
    forall(( member(R, [rdx, r9]), member(Size, [%s]), member(Null, [test, known]) ),
           ( format("case ~w ~w ~w~n", [Null, R, Size]), one(Null, load(R), Size) )),
    forall(( member(Size0, [%s]), member(Size, [%s]), member(Null, [test, known]) ),
           ( phrase(check_share:share_bounds(test, load(r9), Size0, fail), A),
             phrase(check_share:share_bounds(Null, reuse(r9), Size, fail), B),
             append([A, [ins(mov, q, [mem(-8, rbp), reg(rax)])], B], Ls0),
             check_share:shared_uppers(Ls0, Ls),
             format("case reuse-~w ~w ~w~n", [Null, Size0, Size]), print_lines(Ls) )),
    halt)).
""" % (os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src",
                    "check_share"),
       ",".join(map(str, FULL_SIZES)), ",".join(map(str, SIZES)),
       ",".join(map(str, SIZES)))


def emitted():
    """{(kind, a, b): [(op, width, [operand])]} from nanofil."""
    here = os.path.dirname(os.path.abspath(__file__))
    with tempfile.NamedTemporaryFile("w", suffix=".pl") as script:
        script.write(GOAL)
        script.flush()
        out = subprocess.run(
            [os.path.join(here, "..", "bin", "nanofil"), "--script",
             script.name], stdin=subprocess.DEVNULL,
            capture_output=True, text=True, check=True).stdout
    cases, current = {}, None
    for line in out.splitlines():
        words = line.split()
        if words[0] == "case":
            current = cases.setdefault(tuple(words[1:]), [])
        elif words[0] == "ins":
            current.append((words[1], words[2], words[3:]))
    return cases


def run(lines, ptrs, lower, uppers):
    """Interpret lines. %rax starts as ptrs[0]; each reload of %rax from
    -8(%rbp) takes the next of ptrs, and the upper at -16(%rcx) is then the
    next of uppers. Returns (passes, header_ok, checks), where checks
    counts the upper loads."""
    regs = {"rax": ptrs[0], "rcx": lower,
            "rdx": z3.BitVec("rdx0", 64), "r9": z3.BitVec("r90", 64)}
    flags = {}
    alive = z3.BoolVal(True)          # no jump to fail taken yet
    header_ok = z3.BoolVal(True)      # every header read had lower != 0
    phase = [0]
    loads = [0]

    def value(o):
        nonlocal header_ok
        kind, _, rest = o.partition(":")
        if kind == "reg":
            return regs[rest]
        if kind == "imm":
            return z3.BitVecVal(int(rest), 64)
        if kind == "mem":
            d, b = rest.split(":")
            if (int(d), b) == (-8, "rbp"):
                phase[0] += 1
                return ptrs[phase[0]]
            assert (int(d), b) == (-16, "rcx"), o
            header_ok = z3.And(header_ok, z3.Implies(alive, regs["rcx"] != 0))
            loads[0] += 1
            return uppers[phase[0]]
        raise ValueError(o)

    def set_flags(r, cf):
        flags.update(cf=cf, zf=r == 0)

    conds = {"z": lambda: flags["zf"],
             "b": lambda: flags["cf"],
             "a": lambda: z3.And(z3.Not(flags["cf"]), z3.Not(flags["zf"]))}
    for op, width, os_ in lines:
        assert width in ("q", "none"), (op, width)
        if op == "mov":
            regs[os_[1][4:]] = value(os_[0])
        elif op == "lea":
            kind, _, rest = os_[0].partition(":")
            assert kind == "mem", os_
            d, b = rest.split(":")
            regs[os_[1][4:]] = regs[b] + int(d)
        elif op in ("sub", "cmp"):
            a, b = value(os_[0]), value(os_[1])
            r = b - a
            set_flags(r, z3.ULT(b, a))
            if op == "sub":
                regs[os_[1][4:]] = r
        elif op == "test":
            a, b = value(os_[0]), value(os_[1])
            set_flags(b & a, z3.BoolVal(False))
        elif op.startswith("j"):
            assert os_ == ["sym:fail"], os_
            alive = z3.And(alive, z3.Not(conds[op[1:]]()))
        else:
            raise ValueError(op)
        if op == "mov" and os_[0] == "mem:-8:rbp":
            first_passed[0] = alive
    return alive, header_ok, loads[0]


first_passed = [None]


def wide(x):
    return z3.ZeroExt(2, x)


def spec(ptr, lower, upper, size):
    return z3.And(lower != 0, z3.ULE(lower, ptr), wide(ptr) + size <= wide(upper))


def capability(lower, upper, bits):
    return z3.Implies(lower != 0, z3.And(z3.UGE(lower, 16), z3.ULE(lower, upper),
                                         z3.ULT(upper, 1 << bits)))


def prove(assumptions, claim):
    s = z3.Solver()
    s.add(*assumptions, z3.Not(claim))
    r = s.check()
    return None if r == z3.unsat else (s.model() if r == z3.sat else r)


def main():
    ptr0, ptr, lower, upper, freed = z3.BitVecs("ptr0 ptr lower upper freed", 64)
    failures = 0
    for key, lines in sorted(emitted().items()):
        for bits in (47, 56):
            cap = capability(lower, upper, bits)
            if key[0] in ("test", "known"):
                null, reg, size = key[0], key[1], int(key[2])
                first_passed[0] = None
                passes, header_ok, _ = run(lines, [ptr], lower, [upper])
                assume = [cap] + ([lower != 0] if null == "known" else [])
                cex = prove(assume, z3.And(passes == spec(ptr, lower, upper, size), header_ok))
                name = f"{null:5} load({reg}) size {size}"
            else:
                null = key[0].split("-")[1]
                size0, size = int(key[1]), int(key[2])
                first_passed[0] = None
                passes, header_ok, loads = run(lines, [ptr0, ptr], lower, [upper, upper])
                if loads != 1:
                    print(f"reuse {size0}->{size}: {loads} upper loads, expected 1")
                    failures += 1
                cex = prove([cap, first_passed[0]],
                            z3.And(passes == spec(ptr, lower, upper, size), header_ok))
                # Control: the object freed between the checks.
                first_passed[0] = None
                passes_f, _, _ = run(lines, [ptr0, ptr], lower, [upper, lower])
                control = prove([cap, first_passed[0]],
                                passes_f == spec(ptr, lower, lower, size))
                if control is None:
                    print(f"reuse {size0}->{size}: the control was not refuted")
                    failures += 1
                name = f"reuse {null:5} size {size0} then {size}"
            verdict = "equivalent" if cex is None else f"FAILS: {cex}"
            if cex is not None:
                failures += 1
            print(f"{name:32} {bits}-bit  {verdict}")
    if failures:
        print(f"{failures} failures")
        sys.exit(1)
    print("all shared checks proved; every freed-between control refuted")


if __name__ == "__main__":
    main()

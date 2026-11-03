#!/usr/bin/env python3
"""Prove each half check nanofil emits (filc_amd64:half_bounds//5,
docs/half.md) equivalent to Fil-C's full check at the access, given the
facts the validator's half_known/6 establishes, with Z3 over 64-bit
bit-vectors. The sibling of tests/bounds_smt.py (full checks) and
tests/hoist_smt.py (hoisted ones).

The lines come from the compiler itself, through bin/nanofil --script,
and are interpreted with x86-64 semantics, so the proof is about what
nanofil emits.

An earlier check of the same object passed: with lower L, the object's
upper U0 then, and that check's pointer ptr1 (P1 + Lo1 modulo 2^64) and
size S1 (Hi1 - Lo1, 0 < S1 < 2^31):

    L != 0  and  L =< ptr1  and  ptr1 + S1 =< U0       (unbounded integers)

The half check runs later on ptr (P + Lo; P = P1 + D modulo 2^64, the
same lower) for Size bytes, with the object's upper U and flags byte F
then. half_known/6 gives, as integers:

    upper:  ptr = ptr1 + E (mod 2^64), 0 =< E =< 2^62
    lower:  ptr + Size = ptr1 + S1 + F' (mod 2^64), -2^62 =< F' =< 0

and the runtime gives (docs/m7.md, round 4's lifetime lemma, as
hoist_smt.py): U = U0 unless the object was freed since, and then U = L
and FREE (4) is set in F, which is set exactly then; READONLY (2) is
constant; for a nonnull L, 16 =< L =< U0 < 2^Bits, Bits = 47 and 56.
For every bound, selection, size and rights:

    passes  <=>  L != 0  and  L =< ptr  and  ptr + Size =< U
                 and, for a write, the object is not read-only

which is Fil-C's full check (filc_amd64:access_check//2 without its
alignment test, which a half check repeats unchanged). No header byte is
read at a null lower.

Run from nanofil/:  python3 tests/half_smt.py   (needs z3-solver)
"""
import os
import subprocess
import sys
import tempfile

import z3

BOUNDS = ["upper", "lower"]
SELECTIONS = ["stack", "local"]
SIZES = [1, 2, 3, 4, 8, 16, 17, 32, 4096, 2147483647]
NEAR = 1 << 62

GOAL = r"""
:- use_module('%s').
:- initialization((forall(( member(Bound, [%s]), member(Sel, [%s]), member(Size, [%s]), member(Write, [0, 1]) ),
       ( phrase(filc_amd64:half_bounds(Bound, Sel, Size, Write, fail), Is),
         format("case ~w ~w ~w ~w~n", [Bound, Sel, Size, Write]),
         forall(member(ins(Op, W, Os), Is),
                ( format("ins ~w ~w", [Op, W]),
                  forall(member(O, Os),
                         ( O = reg(R) -> format(" reg:~w", [R])
                         ; O = imm(N) -> format(" imm:~w", [N])
                         ; O = mem(D, B) -> format(" mem:~w:~w", [D, B])
                         ; O = sym(S) -> format(" sym:~w", [S]) )),
                  nl )) )), halt)).
""" % (os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src",
                    "filc_amd64"), ",".join(BOUNDS), ",".join(SELECTIONS),
       ",".join(map(str, SIZES)))


def emitted():
    """{(bound, selection, size, write): [(op, width, [operand])]}."""
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
            current = cases.setdefault(
                (words[1], words[2], int(words[3]), int(words[4])), [])
        elif words[0] == "ins":
            current.append((words[1], words[2], words[3:]))
    return cases


def run(lines, ptr, lower, upper, flags_byte):
    """Interpret straight-line lines with ptr in %rax and lower in %rcx;
    every jump goes to fail. Returns (passes, header_ok)."""
    regs = {"rax": ptr, "rcx": lower, "rdx": z3.BitVec("rdx0", 64)}
    flags = {}
    alive = z3.BoolVal(True)
    header_ok = z3.BoolVal(True)

    def value(o, width):
        nonlocal header_ok
        kind, _, rest = o.partition(":")
        if kind == "reg":
            return regs[rest]
        if kind == "imm":
            return z3.BitVecVal(int(rest), 8 if width == "b" else 64)
        if kind == "mem":
            d, b = rest.split(":")
            assert b == "rcx", o
            header_ok = z3.And(header_ok, z3.Implies(alive, regs["rcx"] != 0))
            return {(-16, "q"): upper, (-2, "b"): flags_byte}[(int(d), width)]
        raise ValueError(o)

    conds = {"z": lambda: flags["zf"], "nz": lambda: z3.Not(flags["zf"]),
             "b": lambda: flags["cf"], "ae": lambda: z3.Not(flags["cf"]),
             "a": lambda: z3.And(z3.Not(flags["cf"]), z3.Not(flags["zf"])),
             "l": lambda: flags["lt"]}
    for op, width, os_ in lines:
        if op in ("mov",):
            assert width == "q"
            regs[os_[1][4:]] = value(os_[0], width)
        elif op in ("sub", "cmp"):
            assert width == "q"
            a, b = value(os_[0], width), value(os_[1], width)
            r = b - a
            # lt is SF != OF after b - a: b < a as signed 64-bit values.
            flags.update(cf=z3.ULT(b, a), zf=r == 0, lt=b < a)
            if op == "sub":
                regs[os_[1][4:]] = r
        elif op == "test":
            a, b = value(os_[0], width), value(os_[1], width)
            r = b & a
            flags.update(cf=z3.BoolVal(False), zf=r == 0, lt=r < 0)
        elif op.startswith("j"):
            assert os_ == ["sym:fail"], os_
            alive = z3.And(alive, z3.Not(conds[op[1:]]()))
        else:
            raise ValueError(op)
    return alive, header_ok


def wide(x):
    return z3.ZeroExt(2, x)


def main():
    lower, upper0, ptr1, s1, e = z3.BitVecs("lower upper0 ptr1 s1 e", 64)
    flags_byte = z3.BitVec("flags", 8)
    freed, readonly = z3.Bools("freed readonly")
    failures = 0
    for (bound, sel, size, write), lines in sorted(emitted().items()):
        # e is E (upper) or -F' (lower), both in [0, 2^62].
        if bound == "upper":
            ptr = ptr1 + e
        else:
            ptr = ptr1 + s1 - e - size
        upper = z3.If(freed, lower, upper0)
        passes, header_ok = run(lines, ptr, lower, upper, flags_byte)
        spec = z3.And(lower != 0, z3.ULE(lower, ptr),
                      wide(ptr) + size <= wide(upper))
        if write:
            spec = z3.And(spec, z3.Not(readonly))
        earlier = z3.And(lower != 0, z3.ULE(lower, ptr1),
                         wide(ptr1) + wide(s1) <= wide(upper0),
                         z3.UGE(s1, 1), z3.ULT(s1, 1 << 31),
                         z3.ULE(e, NEAR))
        flag_bits = z3.And((flags_byte & 4 != 0) == freed,
                           (flags_byte & 2 != 0) == readonly)
        for bits in (47, 56):
            capability = z3.And(z3.UGE(lower, 16), z3.ULE(lower, upper0),
                                z3.ULT(upper0, 1 << bits), flag_bits)
            s = z3.Solver()
            s.add(earlier, capability,
                  z3.Or(passes != spec, z3.Not(header_ok)))
            r = s.check()
            name = (f"{bound:5} {sel:5} {'write' if write else 'read':5} "
                    f"size {size:<10} {bits}-bit")
            if r == z3.unsat:
                verdict = "equivalent"
            else:
                m = s.model() if r == z3.sat else None
                verdict = "FAILS: " + (", ".join(
                    f"{v}={hex(m.eval(v).as_long())}"
                    for v in (lower, upper0, ptr1, s1, e)) if m else str(r))
                failures += 1
            print(f"{name}  {verdict}")
    if failures:
        print(f"{failures} failures")
        sys.exit(1)
    print("all half checks proved")


if __name__ == "__main__":
    main()

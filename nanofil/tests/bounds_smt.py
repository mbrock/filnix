#!/usr/bin/env python3
"""Prove each bounds-check shape nanofil emits (filc_amd64:bounds_check//4,
docs/bounds.md) equivalent to Fil-C's condition, with Z3 over 64-bit
bit-vectors.

The lines come from the compiler itself, through bin/nanofil --script, and
are interpreted here with x86-64 semantics for the few instructions they
use, so the proof is about what nanofil emits, not a transcription.

For every shape, selection and access size, with ptr in %rax, lower in
%rcx and upper at -16(lower):

    passes  <=>  lower != 0  and  lower =< ptr  and  ptr + Size =< upper

(ptr + Size in unbounded integers), assuming what Fil-C's runtime
guarantees of a capability whose lower is not 0: the 16-byte header lies
below it (16 =< lower), lower =< upper (free sets upper = lower), and the
object lies in user space, upper < 2^Bits, for Bits = 47 (four-level
paging) and 56 (five-level). A check must also never read the header of
a null lower. ptr is any 64-bit value: integer arithmetic moves a pointer
anywhere without dropping its capability.

--bounds=sign, D. J. Bernstein's proposal, is not equivalent for accesses
of 2 bytes or more; there the script prints a counterexample and proves
the weaker property that every pointer it wrongly passes is
non-canonical, so its access faults in hardware rather than reaching
memory.

Run from nanofil/:  python3 tests/bounds_smt.py [SHAPE...]   (needs z3-solver)
"""
import os
import subprocess
import sys
import tempfile

import z3

SHAPES = sys.argv[1:] or ["split", "merged", "or", "sign"]
SELECTIONS = ["stack", "local"]
SIZES = [1, 2, 3, 4, 8, 16, 17, 32, 4096, 2147483647]

GOAL = r"""
:- use_module('%s').
:- initialization((forall(( member(Shape, [%s]), member(Sel, [%s]), member(Size, [%s]) ),
       ( phrase(filc_amd64:bounds_check(Shape, Sel, Size, fail), Is),
         format("case ~w ~w ~w~n", [Shape, Sel, Size]),
         forall(member(ins(Op, W, Os), Is),
                ( format("ins ~w ~w", [Op, W]),
                  forall(member(O, Os),
                         ( O = reg(R) -> format(" reg:~w", [R])
                         ; O = imm(N) -> format(" imm:~w", [N])
                         ; O = mem(D, B) -> format(" mem:~w:~w", [D, B])
                         ; O = sym(S) -> format(" sym:~w", [S]) )),
                  nl )) )), halt)).
""" % (os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src",
                    "filc_amd64"), ",".join(SHAPES), ",".join(SELECTIONS), ",".join(map(str, SIZES)))


def emitted():
    """{(shape, selection, size): [(op, width, [operand])]} from nanofil."""
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
            current = cases.setdefault((words[1], words[2], int(words[3])), [])
        elif words[0] == "ins":
            current.append((words[1], words[2], words[3:]))
    return cases


def run(lines, ptr, lower, upper):
    """Interpret lines; returns (passes, header_read_ok)."""
    regs = {"rax": ptr, "rcx": lower,
            "rdx": z3.BitVec("rdx0", 64), "rsi": z3.BitVec("rsi0", 64)}
    flags = {}
    alive = z3.BoolVal(True)          # no jump to fail taken yet
    header_ok = z3.BoolVal(True)      # every header read had lower != 0

    def value(o):
        kind, _, rest = o.partition(":")
        if kind == "reg":
            return regs[rest]
        if kind == "imm":
            return z3.BitVecVal(int(rest), 64)
        if kind == "mem":
            d, b = rest.split(":")
            assert (int(d), b) == (-16, "rcx"), o
            nonlocal header_ok
            header_ok = z3.And(header_ok, z3.Implies(alive, regs["rcx"] != 0))
            return upper
        raise ValueError(o)

    def set_flags(r, cf):
        flags.update(cf=cf, zf=r == 0, sf=r < 0)

    conds = {"z": lambda: flags["zf"], "nz": lambda: z3.Not(flags["zf"]),
             "b": lambda: flags["cf"], "ae": lambda: z3.Not(flags["cf"]),
             "a": lambda: z3.And(z3.Not(flags["cf"]), z3.Not(flags["zf"])),
             "s": lambda: flags["sf"]}
    for op, width, os_ in lines:
        assert width in ("q", "none"), (op, width)
        if op == "mov":
            regs[os_[1][4:]] = value(os_[0])
        elif op in ("sub", "cmp"):
            a, b = value(os_[0]), value(os_[1])
            r = b - a
            set_flags(r, z3.ULT(b, a))
            if op == "sub":
                regs[os_[1][4:]] = r
        elif op in ("or", "test"):
            a, b = value(os_[0]), value(os_[1])
            r = (b | a) if op == "or" else (b & a)
            set_flags(r, z3.BoolVal(False))
            if op == "or":
                regs[os_[1][4:]] = r
        elif op == "shr":
            k = int(os_[0][4:])
            assert 0 < k < 64
            b = value(os_[1])
            r = z3.LShR(b, k)
            set_flags(r, z3.Extract(k - 1, k - 1, b) == 1)
            regs[os_[1][4:]] = r
        elif op.startswith("cmov"):
            dst = os_[1][4:]
            regs[dst] = z3.If(conds[op[4:]](), value(os_[0]), regs[dst])
        elif op.startswith("j"):
            assert os_ == ["sym:fail"], os_
            alive = z3.And(alive, z3.Not(conds[op[1:]]()))
        else:
            raise ValueError(op)
    return alive, header_ok


def wide(x):
    return z3.ZeroExt(2, x)


def main():
    ptr, lower, upper = z3.BitVecs("ptr lower upper", 64)
    failures = 0
    for (shape, sel, size), lines in sorted(emitted().items()):
        passes, header_ok = run(lines, ptr, lower, upper)
        spec = z3.And(lower != 0, z3.ULE(lower, ptr),
                      wide(ptr) + size <= wide(upper))
        for bits in (47, 56):
            capability = z3.Implies(
                lower != 0,
                z3.And(z3.UGE(lower, 16), z3.ULE(lower, upper),
                       z3.ULT(upper, 1 << bits)))
            s = z3.Solver()
            s.add(capability, z3.Or(passes != spec, z3.Not(header_ok)))
            r = s.check()
            name = f"{shape:6} {sel:5} size {size:<10} {bits}-bit"
            if r == z3.unsat:
                verdict = "equivalent"
            elif r == z3.sat and shape == "sign":
                m = s.model()
                cex = {v: m.eval(v).as_long() for v in (ptr, lower, upper)}
                # Every wrongly passed pointer is non-canonical under
                # either paging mode: 2^56 =< ptr < 2^64 - 2^56.
                t = z3.Solver()
                t.add(capability, passes, z3.Not(spec),
                      z3.Or(z3.ULT(ptr, 1 << 56),
                            z3.UGE(ptr, (1 << 64) - (1 << 56))))
                if t.check() == z3.unsat:
                    verdict = ("differs, only at non-canonical ptr, e.g. "
                               + ", ".join(f"{k}={hex(v)}" for k, v in
                                           sorted(cex.items(), key=str)))
                else:
                    verdict = f"UNSAFE: {t.model()}"
                    failures += 1
            else:
                verdict = f"FAILS: {s.model() if r == z3.sat else r}"
                failures += 1
            print(f"{name}  {verdict}")
    if failures:
        print(f"{failures} failures")
        sys.exit(1)
    print("all shapes proved")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Prove each hoisted bounds check nanofil emits (filc_amd64:limit_value//3
before a loop, limit_check//3 in it; docs/bounds.md) equivalent to Fil-C's
full check at the access, with Z3 over 64-bit bit-vectors. The sibling of
tests/bounds_smt.py, which proves the unhoisted shapes.

The lines come from the compiler itself, through bin/nanofil --script, and
are interpreted here with x86-64 semantics, including the forward jumps
inside limit_value, so the proof is about what nanofil emits.

The limit is computed once, with lower L in %rcx and the object's upper
U0 at -16(L) then; it is %rdx afterwards. The check runs later with ptr
in %rax, the same L in %rcx, that limit in %rdx and the object's flags
byte F at -2(L). For every shape, access size and rights:

    passes  <=>  L != 0  and  L =< ptr  and  ptr + Size =< U
                 and, for a write, the object is not read-only

where U is the upper at the access (ptr + Size in unbounded integers):
Fil-C's full check (filc_amd64:access_check//2). ptr is any 64-bit value.

What may hold at the loop header, and in between, is explicit:

- the check's lower is the limit's (ir.pl's lower_chain/3: P has P0's
  lower through single-definition flights);
- U = U0 unless the object was freed since, and then U = L (free_impl
  sets upper = lower) and F has FREE (4) set; FREE is set exactly when
  the object is freed (docs/m7.md, round 4's lifetime lemma). A free
  that races with the access is outside this model, as for every check;
- READONLY (2) in F is the read-only flag, constant for the object;
- for a nonnull L, what the runtime guarantees (as bounds_smt.py):
  16 =< L =< U0 < 2^Bits, Bits = 47 and 56 checked separately.

Neither part may read a header (-16(L) or -2(L)) when L is 0, and the
limit's lines must reach their end on every path.

--bounds=sign is inexact here as unhoisted: the script proves that every
pointer it wrongly passes is non-canonical (2^56 =< ptr < 2^64 - 2^56).

Run from nanofil/:  python3 tests/hoist_smt.py [SHAPE...]   (needs z3-solver)
"""
import os
import subprocess
import sys
import tempfile

import z3

SHAPES = sys.argv[1:] or ["split", "merged", "or", "sign"]
SIZES = [1, 2, 3, 4, 8, 10, 16, 17, 32, 4096, 2147483647]

GOAL = r"""
:- use_module('%s').
print_lines(Is) :-
    forall(member(I, Is),
           (   I = label(L) -> format("label ~w~n", [L])
           ;   I = ins(Op, W, Os),
               format("ins ~w ~w", [Op, W]),
               forall(member(O, Os),
                      ( O = reg(R) -> format(" reg:~w", [R])
                      ; O = imm(N) -> format(" imm:~w", [N])
                      ; O = mem(D, B) -> format(" mem:~w:~w", [D, B])
                      ; O = sym(S) -> format(" sym:~w", [S]) )),
               nl )).
:- initialization((forall(( member(Shape, [%s]), member(Size, [%s]), member(Write, [0, 1]) ),
       ( format("case ~w ~w ~w~n", [Shape, Size, Write]),
         phrase(filc_amd64:limit_value(Shape, Size, done), V),
         format("part value~n"), print_lines(V),
         phrase(filc_amd64:limit_check(Shape, Write, fail), C),
         format("part check~n"), print_lines(C) )), halt)).
""" % (os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src",
                    "filc_amd64"), ",".join(SHAPES), ",".join(map(str, SIZES)))


def emitted():
    """{(shape, size, write): {"value": lines, "check": lines}} from nanofil."""
    here = os.path.dirname(os.path.abspath(__file__))
    with tempfile.NamedTemporaryFile("w", suffix=".pl") as script:
        script.write(GOAL)
        script.flush()
        out = subprocess.run(
            [os.path.join(here, "..", "bin", "nanofil"), "--script",
             script.name], stdin=subprocess.DEVNULL,
            capture_output=True, text=True, check=True).stdout
    cases, case, part = {}, None, None
    for line in out.splitlines():
        words = line.split()
        if words[0] == "case":
            case = cases.setdefault(
                (words[1], int(words[2]), int(words[3])), {})
        elif words[0] == "part":
            part = case.setdefault(words[1], [])
        elif words[0] == "label":
            part.append(("label", words[1]))
        else:
            part.append((words[1], words[2], words[3:]))
    return cases


def run(lines, regs, header):
    """Interpret lines from the register values regs (a dict), with the
    header word at -16(%rcx) and the flags byte at -2(%rcx) given by
    header. Jumps go forward, to a label in lines or to `fail`.

    Returns (passes, regs, header_ok): passes holds when the end is
    reached without jumping to fail; header_ok when every header read
    had %rcx != 0."""
    regs = dict(regs)
    flags = {}
    reached = z3.BoolVal(True)
    header_ok = z3.BoolVal(True)
    pending = {}                       # label -> [(condition, regs)]

    def value(o, width):
        nonlocal header_ok
        kind, _, rest = o.partition(":")
        if kind == "reg":
            return regs[rest]
        if kind == "imm":
            return z3.BitVecVal(int(rest), 64 if width == "q" else 8)
        if kind == "mem":
            d, b = rest.split(":")
            assert b == "rcx", o
            header_ok = z3.And(header_ok,
                               z3.Implies(reached, regs["rcx"] != 0))
            return header[(int(d), width)]
        raise ValueError(o)

    def set_flags(r, cf):
        flags.update(cf=cf, zf=r == 0, sf=r < 0)

    conds = {"z": lambda: flags["zf"], "nz": lambda: z3.Not(flags["zf"]),
             "b": lambda: flags["cf"], "ae": lambda: z3.Not(flags["cf"]),
             "a": lambda: z3.And(z3.Not(flags["cf"]), z3.Not(flags["zf"])),
             "s": lambda: flags["sf"]}
    for line in lines:
        if line[0] == "label":
            for c, rs in pending.pop(line[1], []):
                for r in regs:
                    regs[r] = z3.If(c, rs[r], regs[r])
                reached = z3.Or(reached, c)
            flags = {}                 # no flags are live across a label
            continue
        op, width, os_ = line
        if op == "xor":
            # Only the zeroing idiom, 32-bit (which clears the upper half).
            assert width == "l" and os_[0] == os_[1], line
            reg = {"reg:edx": "rdx"}[os_[0]]
            regs[reg] = z3.BitVecVal(0, 64)
            set_flags(regs[reg], z3.BoolVal(False))
        elif op == "mov":
            assert width == "q", line
            regs[os_[1][4:]] = value(os_[0], width)
        elif op in ("sub", "cmp"):
            assert width == "q", line
            a, b = value(os_[0], width), value(os_[1], width)
            r = b - a
            set_flags(r, z3.ULT(b, a))
            if op == "sub":
                regs[os_[1][4:]] = r
        elif op in ("or", "test"):
            a, b = value(os_[0], width), value(os_[1], width)
            r = (b | a) if op == "or" else (b & a)
            set_flags(r, z3.BoolVal(False))
            if op == "or":
                regs[os_[1][4:]] = r
        elif op == "shr":
            k = int(os_[0][4:])
            assert width == "q" and 0 < k < 64
            b = value(os_[1], width)
            r = z3.LShR(b, k)
            set_flags(r, z3.Extract(k - 1, k - 1, b) == 1)
            regs[os_[1][4:]] = r
        elif op.startswith("j"):
            target = os_[0][4:]
            c = conds[op[1:]]()
            if target == "fail":
                reached = z3.And(reached, z3.Not(c))
            else:
                assert any(l == ("label", target) for l in lines), line
                pending.setdefault(target, []).append(
                    (z3.And(reached, c), dict(regs)))
                reached = z3.And(reached, z3.Not(c))
        else:
            raise ValueError(op)
    assert not pending, pending
    return reached, regs, header_ok


def wide(x):
    return z3.ZeroExt(2, x)


def main():
    ptr, lower, upper0 = z3.BitVecs("ptr lower upper0", 64)
    freed, readonly = z3.Bools("freed readonly")
    flags = z3.BitVec("flags", 8)
    scratch = {r: z3.BitVec(r + "0", 64) for r in ("rax", "rdx", "rsi")}
    scratch2 = {r: z3.BitVec(r + "1", 64) for r in ("rdx", "rsi")}
    failures = 0
    for (shape, size, write), parts in sorted(emitted().items()):
        # The limit, before the loop: lower in %rcx, upper0 its header word.
        done, after, value_ok = run(
            parts["value"], dict(scratch, rcx=lower),
            {(-16, "q"): upper0})
        limit = after["rdx"]
        # The access, later: the same lower, the limit in %rdx.
        upper = z3.If(freed, lower, upper0)
        passes, _, check_ok = run(
            parts["check"], dict(scratch2, rax=ptr, rcx=lower, rdx=limit),
            {(-2, "b"): flags})
        spec = z3.And(lower != 0, z3.ULE(lower, ptr),
                      wide(ptr) + size <= wide(upper))
        if write:
            spec = z3.And(spec, z3.Not(readonly))
        flag_bits = z3.And((flags & 4 != 0) == freed,
                           (flags & 2 != 0) == readonly)
        for bits in (47, 56):
            capability = z3.Implies(
                lower != 0,
                z3.And(z3.UGE(lower, 16), z3.ULE(lower, upper0),
                       z3.ULT(upper0, 1 << bits), flag_bits))
            # Only an object can be freed.
            assumptions = z3.And(capability, z3.Implies(freed, lower != 0))
            s = z3.Solver()
            s.add(assumptions,
                  z3.Or(passes != spec, z3.Not(done),
                        z3.Not(value_ok), z3.Not(check_ok)))
            r = s.check()
            name = f"{shape:6} {'write' if write else 'read':5} size {size:<10} {bits}-bit"
            if r == z3.unsat:
                verdict = "equivalent"
            elif r == z3.sat and shape == "sign":
                m = s.model()
                cex = {v: m.eval(v).as_long() for v in (ptr, lower, upper0)}
                t = z3.Solver()
                t.add(assumptions, done, value_ok, check_ok, passes,
                      z3.Not(spec),
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
    print("all hoisted shapes proved")


if __name__ == "__main__":
    main()

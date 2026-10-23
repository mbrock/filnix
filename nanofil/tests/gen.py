#!/usr/bin/env python3
"""Generate random phase-one QBE functions with "# run:" lines.

Usage: gen.py SEED COUNT > file.ssa

Each function mixes straight-line integer ops at both classes, an
optional diamond with a phi, an optional counted loop, and an optional
round trip through stack memory. Inputs favour edge values where signed,
unsigned and width-dependent semantics differ.
"""
import random
import sys

BIN = ["add", "sub", "mul", "and", "or", "xor", "shl", "shr", "sar",
       "div", "rem", "udiv", "urem"]
CMP = ["eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge"]
EXT = ["extsb", "extub", "extsh", "extuh", "extsw", "extuw"]
LOADS = {"l": 8, "sw": 4, "uw": 4, "sh": 2, "uh": 2, "sb": 1, "ub": 1}
STORES = {"l": 8, "w": 4, "h": 2, "b": 1}
EDGES = [0, 1, 2, 3, 7, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256,
         32767, 32768, 65535, 2**31 - 1, 2**31, 2**32 - 1, 2**32,
         2**63 - 1, 2**63, 2**64 - 1, -1, -2, -128, -32768, -2**31]


class Fn:
    def __init__(self, rng, name):
        self.rng = rng
        self.name = name
        self.n = 0
        self.temps = []  # (name, class)
        self.lines = []

    def fresh(self, k, pointer=False):
        """A new temp. Pointers stay out of the operand pool: their values
        are addresses, which differ between the interpreter and native."""
        self.n += 1
        t = f"t{self.n}"
        if not pointer:
            self.temps.append((t, k))
        return t

    def const(self):
        r = self.rng.random()
        if r < 0.5:
            return str(self.rng.choice(EDGES))
        return str(self.rng.randint(-1000, 1000))

    def operand(self, k, exact=False):
        """A value usable at class k: w temps cannot be read as l. With
        exact, only temps of class k itself."""
        pool = [t for t, tk in self.temps
                if tk == k or (k == "w" and not exact)]
        if pool and self.rng.random() < 0.8:
            return "%" + self.rng.choice(pool)
        return self.const()

    def emit(self, s):
        self.lines.append("\t" + s)

    def op(self):
        rng = self.rng
        k = rng.choice("wl")
        r = rng.random()
        if r < 0.6:
            o = rng.choice(BIN)
            if o in ("shl", "shr", "sar"):
                # qbe (1.2 and c081897) emits a constant or constant-folded
                # count as an unmasked immediate, which GNU as rejects
                # outside 8 bits. Mask counts to 0..63 first; the fixtures
                # cover counts at and above the width.
                a = self.operand(k)
                n = self.operand("w")
                b = self.fresh("w")
                self.emit(f"%{b} =w and {n}, 63")
                b = "%" + b
            else:
                a, b = self.operand(k), self.operand(k)
            self.emit(f"%{self.fresh(k)} ={k} {o} {a}, {b}")
        elif r < 0.75:
            ck = rng.choice("wl")
            c = rng.choice(CMP)
            a, b = self.operand(ck), self.operand(ck)
            self.emit(f"%{self.fresh(k)} ={k} c{c}{ck} {a}, {b}")
        elif r < 0.9:
            e = rng.choice(EXT)
            rk = "l" if e in ("extsw", "extuw") else k
            a = self.operand("w")
            self.emit(f"%{self.fresh(rk)} ={rk} {e} {a}")
        else:
            a = self.operand(k)
            self.emit(f"%{self.fresh(k)} ={k} neg {a}")

    def build(self):
        rng = self.rng
        params = [(f"p{i}", rng.choice("wl")) for i in range(rng.randint(1, 3))]
        self.temps = list(params)
        ret = rng.choice("wl")
        out = [f"export function {ret} ${self.name}("
               + ", ".join(f"{k} %{t}" for t, k in params) + ") {", "@start"]
        if rng.random() < 0.4:
            # Initialise the whole slot first so every load is defined.
            p = self.fresh("l", pointer=True)
            self.emit(f"%{p} =l alloc8 16")
            self.emit(f"storel {self.operand('l')}, %{p}")
            q = self.fresh("l", pointer=True)
            self.emit(f"%{q} =l add %{p}, 8")
            self.emit(f"storel {self.operand('l')}, %{q}")
            for _ in range(rng.randint(1, 3)):
                w = rng.choice(list(STORES))
                off = rng.randint(0, 16 - STORES[w])
                a = self.fresh("l", pointer=True)
                self.emit(f"%{a} =l add %{p}, {off}")
                # A sub-word store of a value with bits beyond its width (an
                # l temp, or a constant such as -1) hits a qbe
                # load-forwarding bug (tests/qbe-bugs/storew-l.ssa). Store w
                # temps, and constants reduced to the store width.
                v = self.operand('l' if w == 'l' else 'w', exact=True)
                if w != "l" and not v.startswith("%"):
                    v = str(int(v) % 2 ** (8 * STORES[w]))
                self.emit(f"store{w} {v}, %{a}")
            for _ in range(rng.randint(1, 3)):
                t = rng.choice(list(LOADS))
                off = rng.randint(0, 16 - LOADS[t])
                a = self.fresh("l", pointer=True)
                self.emit(f"%{a} =l add %{p}, {off}")
                k = "l" if t == "l" else rng.choice("wl")
                self.emit(f"%{self.fresh(k)} ={k} load{t} %{a}")
        for _ in range(rng.randint(2, 8)):
            self.op()
        out += self.lines
        self.lines = []
        label = "start"
        if rng.random() < 0.5:
            # Branch on a comparison: qbe miscompiles jnz that reuses the
            # flags of a shift or a 64-bit op (tests/qbe-bugs/jnz-*.ssa).
            v = self.operand(rng.choice("wl"))
            ck = "l" if v.startswith("%") and dict(self.temps)[v[1:]] == "l" else "w"
            c = self.fresh("w")
            out.append(f"\t%{c} =w cne{ck} {v}, 0")
            out.append(f"\tjnz %{c}, @then, @else")
            arms = []
            for arm in ("then", "else"):
                out.append(f"@{arm}")
                saved = list(self.temps)
                for _ in range(rng.randint(1, 3)):
                    self.op()
                v = self.operand(ret)
                self.temps = saved
                out += self.lines
                self.lines = []
                out.append("\tjmp @join")
                arms.append((arm, v))
            out.append("@join")
            j = self.fresh(ret)
            out.append(f"\t%{j} ={ret} phi @then {arms[0][1]}, @else {arms[1][1]}")
            label = "join"
        if rng.random() < 0.4:
            c0 = self.operand("w")
            n = self.fresh("w")
            out.append(f"\t%{n} =w and {c0}, 7")
            init = self.operand(ret)
            out.append("\tjmp @loop")
            out.append("@loop")
            i, i1 = f"i{self.n}", f"i{self.n}n"
            acc, acc1 = f"a{self.n}", f"a{self.n}n"
            out.append(f"\t%{i} =w phi @{label} 0, @loop %{i1}")
            out.append(f"\t%{acc} ={ret} phi @{label} {init}, @loop %{acc1}")
            o = rng.choice(["add", "mul", "xor", "sub"])
            out.append(f"\t%{acc1} ={ret} {o} %{acc}, {self.operand(ret)}")
            out.append(f"\t%{i1} =w add %{i}, 1")
            c = f"c{self.n}"
            out.append(f"\t%{c} =w csltw %{i1}, %{n}")
            out.append(f"\tjnz %{c}, @loop, @exit")
            out.append("@exit")
            self.temps.append((acc1, ret))
        out.append(f"\tret {self.operand(ret)}")
        out.append("}")
        runs = []
        for _ in range(6):
            args = [str(rng.choice(EDGES) if rng.random() < 0.7
                        else rng.randint(-2**63, 2**64 - 1)) for _ in params]
            runs.append(f"# run: ${self.name} " + " ".join(args))
        return "\n".join(runs + out) + "\n"


def main():
    seed, count = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    print(f"# generated by gen.py {seed} {count}\n")
    for i in range(count):
        print(Fn(rng, f"g{i}").build())


if __name__ == "__main__":
    main()

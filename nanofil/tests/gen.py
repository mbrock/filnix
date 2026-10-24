#!/usr/bin/env python3
"""Generate random integer IR functions (src/ir_text.pl) with run/2 facts.

Usage: gen.py SEED COUNT > file.ir

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
EXT = ["sb", "ub", "sh", "uh", "sw", "uw"]
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
            return f"c({self.rng.choice(EDGES)})"
        return f"c({self.rng.randint(-1000, 1000)})"

    def operand(self, k):
        """A value usable at class k: w temps cannot be read as l."""
        pool = [t for t, tk in self.temps if tk == k or k == "w"]
        if pool and self.rng.random() < 0.8:
            return f"t({self.rng.choice(pool)})"
        return self.const()

    def emit(self, s):
        self.lines.append(s)

    def ins(self, d, k, op, args):
        self.emit(f"ins(t({d}), {k}, {op}, [{', '.join(args)}])")

    def op(self):
        rng = self.rng
        k = rng.choice("wl")
        r = rng.random()
        if r < 0.6:
            o = rng.choice(BIN)
            a = self.operand(k)
            b = self.operand("w" if o in ("shl", "shr", "sar") else k)
            self.ins(self.fresh(k), k, o, [a, b])
        elif r < 0.75:
            ck = rng.choice("wl")
            c = rng.choice(CMP)
            a, b = self.operand(ck), self.operand(ck)
            self.ins(self.fresh(k), k, f"cmp({c}, {ck})", [a, b])
        elif r < 0.9:
            e = rng.choice(EXT)
            rk = "l" if e in ("sw", "uw") else k
            a = self.operand("w")
            self.ins(self.fresh(rk), rk, f"ext({e})", [a])
        else:
            a = self.operand(k)
            self.ins(self.fresh(k), k, "neg", [a])

    def build(self):
        rng = self.rng
        params = [(f"p{i}", rng.choice("wl")) for i in range(rng.randint(1, 3))]
        self.temps = list(params)
        ret = rng.choice("wl")
        blocks = []

        def close(label, phis, jump):
            blocks.append((label, phis, self.lines, jump))
            self.lines = []

        if rng.random() < 0.4:
            # Initialise the whole slot first so every load is defined.
            p = self.fresh("l", pointer=True)
            self.ins(p, "l", "alloc(8)", ["c(16)"])
            self.emit(f"store(l, {self.operand('l')}, t({p}))")
            q = self.fresh("l", pointer=True)
            self.ins(q, "l", "add", [f"t({p})", "c(8)"])
            self.emit(f"store(l, {self.operand('l')}, t({q}))")
            for _ in range(rng.randint(1, 3)):
                w = rng.choice(list(STORES))
                off = rng.randint(0, 16 - STORES[w])
                a = self.fresh("l", pointer=True)
                self.ins(a, "l", "add", [f"t({p})", f"c({off})"])
                v = self.operand('l' if w == 'l' else 'w')
                self.emit(f"store({w}, {v}, t({a}))")
            for _ in range(rng.randint(1, 3)):
                t = rng.choice(list(LOADS))
                off = rng.randint(0, 16 - LOADS[t])
                a = self.fresh("l", pointer=True)
                self.ins(a, "l", "add", [f"t({p})", f"c({off})"])
                k = "l" if t == "l" else rng.choice("wl")
                self.ins(self.fresh(k), k, f"load({t})", [f"t({a})"])
        for _ in range(rng.randint(2, 8)):
            self.op()
        label, phis = "start", []
        if rng.random() < 0.5:
            close(label, phis, f"jnz({self.operand('w')}, then, else)")
            arms = []
            for arm in ("then", "else"):
                saved = list(self.temps)
                for _ in range(rng.randint(1, 3)):
                    self.op()
                v = self.operand(ret)
                self.temps = saved
                close(arm, [], "jmp(join)")
                arms.append((arm, v))
            j = self.fresh(ret)
            label = "join"
            phis = [f"phi(t({j}), {ret}, [then-{arms[0][1]}, else-{arms[1][1]}])"]
        if rng.random() < 0.4:
            c0 = self.operand("w")
            n = self.fresh("w")
            self.ins(n, "w", "and", [c0, "c(7)"])
            init = self.operand(ret)
            close(label, phis, "jmp(loop)")
            i, i1 = f"i{self.n}", f"i{self.n}n"
            acc, acc1 = f"a{self.n}", f"a{self.n}n"
            phis = [f"phi(t({i}), w, [{label}-c(0), loop-t({i1})])",
                    f"phi(t({acc}), {ret}, [{label}-{init}, loop-t({acc1})])"]
            o = rng.choice(["add", "mul", "xor", "sub"])
            self.ins(acc1, ret, o, [f"t({acc})", self.operand(ret)])
            self.ins(i1, "w", "add", [f"t({i})", "c(1)"])
            c = f"c{self.n}"
            self.ins(c, "w", "cmp(slt, w)", [f"t({i1})", f"t({n})"])
            close("loop", phis, f"jnz(t({c}), loop, exit)")
            label, phis = "exit", []
            self.temps.append((acc1, ret))
        close(label, phis, f"ret({self.operand(ret)})")
        runs = []
        for _ in range(6):
            args = [str(rng.choice(EDGES) if rng.random() < 0.7
                        else rng.randint(-2**63, 2**64 - 1)) for _ in params]
            runs.append(f"run({self.name}, [{', '.join(args)}]).")
        out = [f"func({self.name}, export, {ret}, ["
               + ", ".join(f"par({k}, t({t}))" for t, k in params) + "], ["]
        out.append(",\n".join(block(*b) for b in blocks))
        out.append("]).")
        return "\n".join(runs + out) + "\n"


def block(label, phis, insts, jump):
    def lines(xs):
        if not xs:
            return "[]"
        return "[\n" + ",\n".join("        " + x for x in xs) + "\n    ]"
    return f"    blk({label}, {lines(phis)}, {lines(insts)}, {jump})"


def main():
    seed, count = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    print(f"% generated by gen.py {seed} {count}\n")
    for i in range(count):
        print(Fn(rng, f"g{i}").build())


if __name__ == "__main__":
    main()

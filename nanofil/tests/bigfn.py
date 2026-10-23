#!/usr/bin/env python3
"""Generate one large structured C function, for the middle-end
benchmark (bench-cfg.pl) and as translation-validation corpus.

Usage: bigfn.py SEED STATEMENTS > file.c

The function has a dozen unsigned locals and a random tree of
assignments, if/else, bounded loops and early returns, the shape of
ordinary code: hundreds of blocks with small live sets (each temp lives
within a statement, each local is one slot until promote). Arithmetic is
unsigned and shifts are by 0..7, so there is no undefined behaviour and
clang must agree with nanofil. Every loop runs at most 7 or 32 times.
The output needs no headers, and ends with "// run:" lines for
difftest.sh.
"""
import random
import sys

VARS = [f"v{i}" for i in range(12)]


def expr(rng, depth=0):
    if depth > 2 or rng.random() < 0.4:
        return rng.choice(VARS + [str(rng.randint(0, 99))])
    op = rng.choice(["+", "-", "*", "&", "|", "^", "<", "==", ">>", "<<"])
    if op in (">>", "<<"):
        return f"({expr(rng, depth + 1)} {op} {rng.randint(0, 7)})"
    return f"({expr(rng, depth + 1)} {op} {expr(rng, depth + 1)})"


def block(rng, budget, n, depth, out, ind):
    """Up to n statements, each counted against the shared budget."""
    for _ in range(n):
        if budget[0] <= 0:
            return
        budget[0] -= 1
        r = rng.random()
        pad = "    " * ind
        if r < 0.45 or depth > 4:
            out.append(f"{pad}{rng.choice(VARS)} = {expr(rng)};")
        elif r < 0.65:
            out.append(f"{pad}if ({expr(rng)}) {{")
            block(rng, budget, rng.randint(1, 6), depth + 1, out, ind + 1)
            out.append(f"{pad}}} else {{")
            block(rng, budget, rng.randint(1, 6), depth + 1, out, ind + 1)
            out.append(f"{pad}}}")
        elif r < 0.8:
            c = rng.choice(VARS)
            out.append(f"{pad}for (unsigned i{depth} = 0; i{depth} < ({c} & 7); i{depth}++) {{")
            block(rng, budget, rng.randint(1, 6), depth + 1, out, ind + 1)
            out.append(f"{pad}}}")
        elif r < 0.92:
            c = rng.choice(VARS)
            out.append(f"{pad}for (unsigned w{depth} = {c}; w{depth} > 0; w{depth} = w{depth} / 2) {{")
            block(rng, budget, rng.randint(1, 4), depth + 1, out, ind + 1)
            out.append(f"{pad}}}")
        else:
            out.append(f"{pad}if ({expr(rng)} == 17) return {expr(rng)};")


def main():
    seed, n = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    out = ["unsigned big(unsigned a, unsigned b) {"]
    for i, v in enumerate(VARS):
        out.append(f"    unsigned {v} = {'a' if i % 2 else 'b'} + {i};")
    budget = [n]
    while budget[0] > 0:
        block(rng, budget, 1, 0, out, 1)
    out.append("    return " + " + ".join(VARS) + ";")
    out.append("}")
    for a, b in [(0, 0), (1, 2), (17, 4294967295), (123456789, 42), (2**31, 7)]:
        out.append(f"// run: $big {a} {b}")
    print("\n".join(out))


main()

#!/usr/bin/env python3
"""Generate a program whose one function keeps N ints live together and
writes each of them twice, so under -O each is a register-home candidate
that interferes with all the others: about N^2/2 interference pairs.
The allocator once listed every pair with a bignum bitset of its own and
overflowed the 4 GB stack on netcdf's tst_h_atts.c and openssh's libcrux
(docs/perf.md, item 13).

Usage: manyhomes.py N > file.c
"""
import sys

n = int(sys.argv[1])
lines = ["#include <stdio.h>", "", "__attribute__((noinline)) unsigned f(volatile unsigned *a) {"]
lines += [f"    unsigned v{i} = a[{i % 64}] + {i};" for i in range(n)]
lines += [f"    v{i} ^= v{(i * 7 + 3) % n} * {i % 13 + 1}u;" for i in range(n)]
lines.append("    unsigned s = 0;")
lines += [f"    s = s * 31u + v{i};" for i in range(n)]
lines += ["    return s;", "}", "",
          "int main(void) {",
          "    static volatile unsigned a[64];",
          "    for (unsigned i = 0; i < 64; i++) a[i] = i * 2654435761u;",
          '    printf("%u\\n", f(a));',
          "    return 0;",
          "}"]
print("\n".join(lines))

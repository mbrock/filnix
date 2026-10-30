#!/usr/bin/env python3
"""Generate a program whose one function is a single basic block of N
statements over a small array, as macro-unrolled crypto is (tor's
keccak-tiny-unrolled.c: one block of 95k IR lines). Block liveness once
grew a gen and kill set per instruction, quadratic in the block's length:
that file took over 10 minutes to compile plain (docs/perf.md, item 15).

Usage: longblock.py N > file.c
"""
import sys

n = int(sys.argv[1])
lines = ["#include <stdio.h>", "#include <stdint.h>", "",
         "__attribute__((noinline)) void mix(uint64_t *a) {",
         "    uint64_t t = a[1];"]
for i in range(n):
    x, y, z = i % 25, (i * 7 + 3) % 25, (i * 11 + 5) % 25
    lines.append(f"    a[{x}] ^= (a[{y}] << {i % 63 + 1} | a[{y}] >> {63 - i % 63}) ^ (~a[{z}] & t);")
    lines.append(f"    t += a[{x}] + {i}u;")
lines += ["}", "",
          "int main(void) {",
          "    uint64_t a[25];",
          "    for (int i = 0; i < 25; i++) a[i] = 0x9e3779b97f4a7c15u * (i + 1);",
          "    mix(a);",
          "    uint64_t s = 0;",
          "    for (int i = 0; i < 25; i++) s = s * 31 + a[i];",
          '    printf("%llu\\n", (unsigned long long)s);',
          "    return 0;",
          "}"]
print("\n".join(lines))

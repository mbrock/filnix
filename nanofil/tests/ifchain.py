#!/usr/bin/env python3
"""Generate a program whose one function is a chain of N `if` arms, each
reading fields of one struct around a call, so each arm's checks have
every earlier arm's checks of the same object as candidate sources.
Renewal once walked up the dominator tree for every (check, source)
pair: with -O's combined checks, 600 arms took 189 s to compile (the
combined default's review; docs/perf.md, item 18).

Usage: ifchain.py N > file.c
"""
import sys

n = int(sys.argv[1])
lines = ["#include <stdio.h>", "",
         "struct S { long f[64]; struct S *p; };",
         "static long calls;",
         "__attribute__((noinline)) void g(struct S *s) { calls += s->f[1]; }",
         "__attribute__((noinline)) long h(struct S *s, long n) {",
         "    long x = 0;"]
lines += [f"    if (n == {i}) {{ x += s->f[{i % 64}]; g(s); x += s->p->f[{i * 7 % 64}] + s->f[{(i + 3) % 64}]; }}"
          for i in range(n)]
lines += ["    return x;", "}", "",
          "int main(void) {",
          "    static struct S a, b;",
          "    for (int i = 0; i < 64; i++) { a.f[i] = i; b.f[i] = 100 + i; }",
          "    a.p = &b;",
          "    long t = 0;",
          f"    for (long n = 0; n < {n}; n += 7) t += h(&a, n);",
          '    printf("%ld %ld\\n", t, calls);',
          "    return 0;",
          "}"]
print("\n".join(lines))

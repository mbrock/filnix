#!/usr/bin/env python3
"""Generate a program whose one function copies a large pointer-free
struct by value, twice: minizip's zipOpen3 (`*zi = ziinit` of a 64 KB
struct) has this shape. The frontend expands each copy into a load and
a store per word, so the function has tens of thousands of instructions,
each loaded word its own register-home candidate under -O. The register
checker's live sets once grew with lines × homes and overflowed the
1 GB stack on it (docs/perf.md, item 11).

Usage: bigcopy.py BYTES > file.c
"""
import sys

n = int(sys.argv[1])
print(f"""#include <stdio.h>
#include <stdlib.h>

struct big {{ unsigned char buf[{n}]; unsigned long keys[3]; int count; }};

struct big *copy(struct big *src) {{
    struct big local = *src;
    local.count++;
    local.keys[1] ^= local.buf[{n // 2}];
    struct big *p = malloc(sizeof *p);
    if (!p) return 0;
    *p = local;
    return p;
}}

int main(void) {{
    struct big *s = calloc(1, sizeof *s);
    for (unsigned i = 0; i < {n}; i++) s->buf[i] = (unsigned char)(i * 7 + 3);
    s->keys[1] = 5;
    struct big *d = copy(s);
    unsigned long sum = d->count + d->keys[1];
    for (unsigned i = 0; i < {n}; i++) sum = sum * 31 + d->buf[i];
    printf("%lu\\n", sum);
    return 0;
}}""")

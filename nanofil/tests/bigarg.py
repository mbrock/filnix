#!/usr/bin/env python3
"""Generate a reproducer for a known limit (docs/m4.md, Known gaps): a
large struct, which holds a pointer, passed and returned by value. In
the IR a struct argument is one argument per eightbyte (a 64 KB one is
8193), so the callee's word list, and the caller's word loads and
stores, grow with the struct. At 65536 bytes `nanofil -O cc` ran out of
the 1 GB stack in amd64_regs after 5.5 minutes (91746a6), while filcc
emits about 1,000 lines with four memmove calls. Copies by assignment,
initialization and return already go through zmemmove; only by-value
arguments remain. It is not in any suite.

Usage: bigarg.py BYTES > file.c
"""
import sys

n = int(sys.argv[1])
print(f"""#include <stdio.h>
#include <stdlib.h>

struct big {{ unsigned char buf[{n}]; int *p; }};

long take(struct big b) {{ return b.buf[7] + *b.p; }}
struct big give(struct big *s) {{ return *s; }}
long call(struct big *s) {{ return take(*s); }}
struct big g;
void ret(struct big *s) {{ g = give(s); }}

int main(void) {{
    static int x = 35;
    struct big *s = calloc(1, sizeof *s);
    s->buf[7] = 7;
    s->p = &x;
    ret(s);
    printf("%ld %ld\\n", call(s), take(g));
    return 0;
}}""")

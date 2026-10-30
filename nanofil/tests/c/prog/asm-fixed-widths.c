/* asm_fixed operands of other widths, as clang gives them: an input tied
   to a wider output is zero-extended to the output's width; an output
   takes its place's type, a bit-field's included; a _Bool output, in a
   register cpuid writes or passed through, takes bit 0. */
#include <stdio.h>
#include <stdbool.h>

struct S { unsigned long bf : 40; long sb : 40; bool bb : 1; } s;

int main(void) {
    unsigned a, b, c, d;
    long o1, o2, o3;
    int in = -1;
    signed char sc = -1;
    enum { M1 = -1 } e = M1;
    unsigned v = 0xffffffffu, w = 0x80000000u;
    int two = 2;
    long big = 0x100000000L;
    bool o;

    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(o1) : "0"(0), "2"(0), "4"(in));
    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(o2) : "0"(0), "2"(0), "4"(sc));
    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(o3) : "0"(0), "2"(0), "4"(e));
    printf("tied %lx %lx %lx\n", o1, o2, o3);

    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(s.bf) : "0"(0), "2"(0), "4"(v));
    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(s.sb) : "0"(0), "2"(0), "4"(w));
    printf("bit-fields %lx %lx\n", (unsigned long)s.bf, (long)s.sb);

    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(s.bb) : "0"(0), "2"(0), "4"(two));
    printf("bool field from 2: %d\n", s.bb);
    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(o) : "0"(0), "2"(0), "4"(two));
    printf("bool from 2: %d\n", o);
    __asm__ volatile("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(o) : "0"(0), "2"(0), "4"(big));
    printf("bool from 1<<32: %d\n", o);
    __asm__ volatile("cpuid" : "=a"(s.bb), "=b"(b), "=c"(c), "=d"(d) : "0"(0), "2"(0));
    printf("bool field from eax: %d\n", s.bb == (a & 1));
    return 0;
}

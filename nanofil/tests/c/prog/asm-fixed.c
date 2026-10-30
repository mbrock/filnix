/* Fixed-register inline asm that filcc passes through runs natively
   (asm_fixed, docs/asm-fixed.md), in the forms of the survey packages. */
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

static void cpuid_plain(unsigned leaf, unsigned r[4]) {      /* libblake3: no ecx input */
    __asm__ __volatile__("cpuid" : "=a"(r[0]), "=b"(r[1]), "=c"(r[2]), "=d"(r[3]) : "a"(leaf));
}
static void cpuid_count(unsigned leaf, unsigned sub, unsigned r[4]) {
    __asm__("cpuid" : "=a"(r[0]), "=b"(r[1]), "=c"(r[2]), "=d"(r[3]) : "a"(leaf), "c"(sub));
}
static void cpuid_tied(unsigned leaf, unsigned sub, unsigned r[4]) {  /* pcre2, util-linux */
    unsigned a, b, c, d;
    __asm__ __volatile__("cpuid\n\t" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "0"(leaf), "2"(sub));
    r[0] = a; r[1] = b; r[2] = c; r[3] = d;
}
static void cpuid_plus(unsigned leaf, unsigned r[4]) {       /* fftw: "+b" and "+d" dropped */
    unsigned a = leaf, b = 0x1234, c = 0, d = 0x5678;
    __asm__ volatile("cpuid" : "+a"(a), "+b"(b), "+c"(c), "+d"(d));
    r[0] = a; r[1] = b; r[2] = c; r[3] = d;
}
static void show(const char *n, unsigned leaf, unsigned r[4]) {
    if (leaf == 1) r[1] &= 0x00ffffff;   /* the APIC id is the core's */
    printf("%s %08x %08x %08x %08x\n", n, r[0], r[1], r[2], r[3]);
}
int main(void) {
    unsigned r[4];
    cpuid_plain(0, r); show("plain0", 0, r);
    cpuid_plain(1, r); show("plain1", 1, r);
    cpuid_count(7, 0, r); show("count7", 7, r);
    cpuid_tied(7, 0, r); show("tied7", 7, r);
    cpuid_plus(0, r); show("plus0", 0, r);
    uint64_t wide;                        /* a 64-bit output is zero-extended */
    __asm__("cpuid" : "=a"(wide) : "a"(0x80000000u) : "ebx", "ecx", "edx");
    printf("wide %d\n", (int)(wide >> 32));
    bool b;
    __asm__("cpuid" : "=a"(b) : "a"(0) : "%rbx", "rcx", "rdx");
    printf("bool %d\n", (int)b);
    long sl = -1;                         /* the input's low 32 bits */
    unsigned lo0;
    __asm__("cpuid" : "=a"(lo0) : "a"(sl & 0xffffffff00000000L) : "rbx", "rcx", "rdx", "memory");
    printf("trunc %08x\n", lo0);
    if (r[2] & (1u << 27)) {              /* OSXSAVE: xgetbv */
        unsigned xlo, xhi;
        __asm__ volatile("xgetbv" : "=a"(xlo), "=d"(xhi) : "c"(0));
        unsigned yhi, ylo;
        __asm__ volatile("xgetbv" : "=d"(yhi), "=a"(ylo) : "c"(0));   /* libdeflate */
        printf("xgetbv %d\n", xlo == ylo && xhi == yhi && (xlo & 1));
    }
    unsigned lo, hi, lo2, hi2;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    __asm__ volatile("lfence;");
    __asm__ volatile("\n\tsfence\n");
    __asm__ volatile("mfence" ::: "memory");
    __asm__ volatile("pause");
    __asm__ volatile("  RDTSC  " : "=a"(lo2), "=d"(hi2));
    uint64_t t1 = (uint64_t)hi << 32 | lo, t2 = (uint64_t)hi2 << 32 | lo2;
    printf("rdtsc %d\n", t2 > t1);
    unsigned keep = 99;                   /* "+S" passes through: not written */
    __asm__("cpuid" : "=a"(lo), "+S"(keep) : "a"(0) : "rbx", "rcx", "rdx");
    printf("keep %u\n", keep);
    return 0;
}

/* nanofil refuses __int128, so it does not define __SIZEOF_INT128__,
   and a program that tests for it takes its portable path, as
   coreutils' factor.c does for its double-word multiply (umul_ppmm).
   clang's build takes the __int128 path; both must agree. */
#include <stdint.h>
#include <stdio.h>
static void umul(uint64_t u, uint64_t v, uint64_t *hi, uint64_t *lo) {
#ifdef __SIZEOF_INT128__
    unsigned __int128 w = (unsigned __int128)u * v;
    *hi = (uint64_t)(w >> 64); *lo = (uint64_t)w;
#else
    uint64_t ul = u & 0xffffffff, uh = u >> 32, vl = v & 0xffffffff, vh = v >> 32;
    uint64_t x0 = ul * vl, x1 = ul * vh, x2 = uh * vl, x3 = uh * vh;
    x1 += x0 >> 32;
    x1 += x2;
    if (x1 < x2) x3 += 1ull << 32;
    *hi = x3 + (x1 >> 32); *lo = (x1 << 32) + (x0 & 0xffffffff);
#endif
}
int main(void) {
    uint64_t vs[] = { 0, 1, 3, 0xffffffff, 0x100000000, 0xdeadbeefcafebabe, UINT64_MAX };
    for (unsigned i = 0; i < 7; i++)
        for (unsigned j = 0; j < 7; j++) {
            uint64_t hi, lo;
            umul(vs[i], vs[j], &hi, &lo);
            printf("%016llx%016llx\n", (unsigned long long)hi, (unsigned long long)lo);
        }
    return 0;
}

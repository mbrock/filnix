/* Classifying a long double reads its x87 bits as clang does: unnormals,
   pseudo-infinities and pseudo-NaNs are NaNs, and a pseudo-denormal is
   FP_NORMAL to fpclassify but not isnormal (redis util.c's isinf and
   isnan on a long double). */
#include <math.h>
#include <stdio.h>
#include <string.h>
static long double make(unsigned short se, unsigned long long sig) {
    long double x = 0; unsigned char b[16] = {0};
    memcpy(b, &sig, 8); memcpy(b + 8, &se, 2); memcpy(&x, b, 10); return x;
}
static volatile int z;
int main(void) {
    struct { const char *n; unsigned short se; unsigned long long sig; } c[] = {
        {"zero", 0, 0}, {"-zero", 0x8000, 0}, {"one", 0x3fff, 1ull << 63}, {"-one", 0xbfff, 1ull << 63},
        {"denormal", 0, 1}, {"-denormal", 0x8000, 0x7fffffffffffffffull}, {"pseudo-denormal", 0, 1ull << 63 | 5},
        {"min-normal", 1, 1ull << 63}, {"max", 0x7ffe, ~0ull}, {"inf", 0x7fff, 1ull << 63}, {"-inf", 0xffff, 1ull << 63},
        {"qnan", 0x7fff, 3ull << 62}, {"snan", 0x7fff, 1ull << 63 | 1}, {"-qnan", 0xffff, 3ull << 62},
        {"pseudo-inf", 0x7fff, 0}, {"pseudo-nan", 0x7fff, 1}, {"unnormal", 0x3fff, 1ull << 62}, {"-unnormal-0", 0xc000, 0},
    };
    for (unsigned i = 0; i < sizeof c / sizeof c[0]; i++) {
        long double v = make(c[i].se, c[i].sig);
        if (z) v += 1;
        printf("%-16s nan %d inf %d isinf %d finite %d normal %d class %d sign %d\n", c[i].n,
               isnan(v) != 0, isinf(v), __builtin_isinf(v), isfinite(v) != 0, isnormal(v) != 0,
               fpclassify(v), signbit(v) != 0);
    }
    return 0;
}

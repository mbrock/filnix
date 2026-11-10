/* Under -fno-math-errno, as glibc's libm is built, __builtin_sqrt and
   its f and l forms are the IR's sqrt (sqrtsd, sqrtss, fsqrt), and
   __builtin_trunc and truncf are built from a conversion through the
   integer below 2^52 (2^23): glibc's own sqrt and trunc are these
   builtins, so neither may be a call. Bits are printed so a wrong
   rounding, a lost -0 or an unquieted NaN shows. */
// cflags: -fno-math-errno
#include <stdio.h>
#include <string.h>
#include <stdint.h>

static uint64_t dbits(double x) { uint64_t b; memcpy(&b, &x, 8); return b; }
static uint32_t fbits(float x) { uint32_t b; memcpy(&b, &x, 4); return b; }
static double dval(uint64_t b) { double x; memcpy(&x, &b, 8); return x; }
static float fval(uint32_t b) { float x; memcpy(&x, &b, 4); return x; }

static void ld(long double x)
{
    long double r = __builtin_sqrtl(x);
    unsigned char b[16] = {0};
    memcpy(b, &r, 10);
    for (int i = 9; i >= 0; i--) printf("%02x", b[i]);
    printf("\n");
}

int main(void)
{
    uint64_t ds[] = { 0x4000000000000000, 0x3ff0000000000001, 0x0000000000000001,
                      0x000fffffffffffff, 0x8000000000000000, 0xbff0000000000000,
                      0x7ff0000000000000, 0xfff0000000000000, 0x7ff4000000000000,
                      0x7fefffffffffffff, 0x4024000000000000 };
    for (unsigned i = 0; i < sizeof ds / sizeof ds[0]; i++)
        printf("sqrt %016llx %016llx\n", (unsigned long long)ds[i],
               (unsigned long long)dbits(__builtin_sqrt(dval(ds[i]))));
    uint32_t fs[] = { 0x40000000, 0x3f800001, 0x00000001, 0x80000000, 0xbf800000,
                      0x7f800000, 0x7fa00000, 0x7f7fffff };
    for (unsigned i = 0; i < sizeof fs / sizeof fs[0]; i++)
        printf("sqrtf %08x %08x\n", fs[i], fbits(__builtin_sqrtf(fval(fs[i]))));
    ld(2.0L); ld(0.0L); ld(-0.0L); ld(1e-4000L); ld(-1.0L);
    double ts[] = { 2.7, -2.7, -0.5, 0.5, -0.0, 4503599627370495.5, 4503599627370496.0,
                    -9007199254740993.0, 1e300, -1e-300, 1.0 / 0.0, -1.0 / 0.0 };
    for (unsigned i = 0; i < sizeof ts / sizeof ts[0]; i++)
        printf("trunc %016llx %016llx\n", (unsigned long long)dbits(ts[i]),
               (unsigned long long)dbits(__builtin_trunc(ts[i])));
    printf("trunc nan %016llx\n", (unsigned long long)dbits(__builtin_trunc(dval(0x7ff4000000000000))));
    float tfs[] = { 2.7f, -2.7f, -0.5f, 8388607.5f, 8388608.0f, -16777217.0f, 3e38f, 1.0f / 0.0f };
    for (unsigned i = 0; i < sizeof tfs / sizeof tfs[0]; i++)
        printf("truncf %08x %08x\n", fbits(tfs[i]), fbits(__builtin_truncf(tfs[i])));
    printf("truncf nan %08x\n", fbits(__builtin_truncf(fval(0x7fa00000))));
    return 0;
}

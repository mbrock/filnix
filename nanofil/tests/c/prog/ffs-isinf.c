/* __builtin_ffs, ffsl and ffsll (cogl), and __builtin_isinf (libpq's
   snprintf.c), as GCC and clang define them. */
#include <stdio.h>
#include <math.h>

static volatile long vals[] = {0, 1, 2, 3, 0x50, -1, 0x80000000L, 0x100000000L,
                               (long)(1UL << 63), -0x7fffffffffffffffL - 1 + 0x10};

int main(void)
{
    for (unsigned i = 0; i < sizeof vals / sizeof vals[0]; i++) {
        long v = vals[i];
        printf("%d %d %d|", __builtin_ffs((int)v), __builtin_ffsl(v), __builtin_ffsll((long long)v));
    }
    printf("\n%d %d\n", __builtin_ffs(0), __builtin_ffsl(1L << 40));
    volatile double d[] = {1.0, INFINITY, -INFINITY, NAN, 0.0, 1e308 * 10};
    volatile float f = -INFINITY;
    for (unsigned i = 0; i < 6; i++)
        printf("%d", __builtin_isinf(d[i]));
    printf(" %d\n", __builtin_isinf(f));
    return 0;
}

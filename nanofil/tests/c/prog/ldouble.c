// link: lib/ldouble.c
/* long double across the nanofil/clang boundary: x87 80-bit values as
   scalars, in structs and through varargs, directly, indirectly and
   with wrong prototypes, both ways. Each value keeps all 64 significand
   bits, which %La shows. The last line reads past a buffer through a
   pointer that came back beside a long double, so its capability
   survived: both builds trap there. */
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include "lib/ldouble.h"

long double n_scale(long double x, int n) { return x * n - 0x1p-62L; }
long double n_mix(int i, long double a, double d, struct ld1 s, int j, struct ld2 t)
{
    return i * 2 + a * 4 + d * 6 + s.v * 8 + j * 10 + t.a * 12 + t.b;
}
struct ld1 n_ld1(long double x) { struct ld1 s = { x * 7 }; return s; }
struct ld2 n_ld2(long double a, long double b) { struct ld2 s = { a + b, a * b }; return s; }
struct ldp n_ldp(char *p, long double v) { struct ldp s = { v / 4, p + 5 }; return s; }
long double n_vsum(int n, ...)
{
    va_list ap;
    va_start(ap, n);
    long double s = 0;
    for (int i = 0; i < n; i++) {
        int k = va_arg(ap, int);
        long double v = va_arg(ap, long double);
        struct ld2 t = va_arg(ap, struct ld2);
        s += k * v - t.a + t.b;
    }
    va_end(ap);
    return s;
}

int main(void)
{
    char *buf = calloc(16, 1);
    for (int i = 0; i < 15; i++)
        buf[i] = 'a' + i;
    struct ld1 s = { 1.0L / 7 };
    struct ld2 t = { 0x1p-61L, 2.0L / 3 };
    printf("scale %La %La\n", c_scale(1.0L + 0x1p-62L, 3), n_scale(1.0L + 0x1p-62L, 3));
    printf("mix %La %La\n", c_mix(1, 0.1L, 0.2, s, 3, t), n_mix(1, 0.1L, 0.2, s, 3, t));
    struct ld1 a = c_ld1(1.0L);
    struct ld2 b = c_ld2(1.0L, 0x1p-63L);
    struct ldp p = c_ldp(buf, 0.75L);
    printf("structs %La %La %La %La %c\n", a.v, b.a, b.b, p.v, *p.p);
    printf("vsum %La %La\n", c_vsum(2, 3, 0.25L, t, 5, 1.0L + 0x1p-60L, t),
           n_vsum(2, 3, 0.25L, t, 5, 1.0L + 0x1p-60L, t));

    long double (*volatile fp)(long double, int) = c_scale;
    struct ld2 (*volatile f2)(long double, long double) = c_ld2;
    long double (*volatile vp)(int, ...) = c_vsum;
    struct ld2 b2 = f2(3.0L, 0.5L);
    printf("indirect %La %La %La %La\n", fp(0.1L, 9), b2.a, b2.b, vp(1, 2, 0.5L, t));

    long double (*volatile w)(long double, int, long) =
        (long double (*)(long double, int, long))(void *)c_scale;
    double (*volatile w2)(long double, int) = (double (*)(long double, int))(void *)c_scale;
    double bits = w2(1.5L, 1);
    unsigned long u;
    memcpy(&u, &bits, 8);
    printf("generic %La %lx\n", w(2.0L / 3, 2, 99), u);
    printf("calls back %La\n", c_calls_back(buf));
    printf("generic back %La\n", c_generic());
    printf("print %Lg %.25Lf %Le %d\n", 1.0L / 3, 0.1L, -1e4000L, (int)sizeof(long double));
    fflush(stdout);
    struct ldp far = c_ldp(buf, 0);
    printf("past end %c\n", far.p[14]);
    return 0;
}

/* The clang side of ldouble.c. */
#include <stdarg.h>
#include <string.h>
#include "ldouble.h"

long double c_scale(long double x, int n) { return x * n + 0x1p-63L; }
long double c_mix(int i, long double a, double d, struct ld1 s, int j, struct ld2 t)
{
    return i + a * 3 + d * 5 + s.v * 7 + j * 11 + t.a * 13 + t.b;
}
struct ld1 c_ld1(long double x) { struct ld1 s = { x / 3 }; return s; }
struct ld2 c_ld2(long double a, long double b) { struct ld2 s = { b, a - b }; return s; }
struct ldp c_ldp(char *p, long double v) { struct ldp s = { v + 1, p + 2 }; return s; }
long double c_vsum(int n, ...)
{
    va_list ap;
    va_start(ap, n);
    long double s = 0;
    for (int i = 0; i < n; i++) {
        int k = va_arg(ap, int);
        long double v = va_arg(ap, long double);
        struct ld2 t = va_arg(ap, struct ld2);
        s += k * v + t.a - t.b;
    }
    va_end(ap);
    return s;
}

long double c_calls_back(char *buf)
{
    struct ld1 s = { 0.1L };
    struct ld2 t = { 1.0L / 3, 0x1p-62L };
    long double (*volatile fp)(long double, int) = n_scale;
    struct ld2 (*volatile f2)(long double, long double) = n_ld2;
    struct ldp q = n_ldp(buf, 2.5L);
    struct ld2 u = f2(1.0L + 0x1p-63L, 0.5L);
    return n_scale(1.0L + 0x1p-62L, 3) + fp(0.1L, 7) + n_mix(1, 0.2L, 0.3, s, 4, t)
         + n_ld1(0.7L).v + u.a + u.b + q.v + *q.p
         + n_vsum(2, 3, 0.25L, t, 5, 1.0L + 0x1p-60L, t);
}

/* Wrong prototypes: an extra argument, and a double read from the
   first eight bytes of a long double result. */
long double c_generic(void)
{
    long double (*volatile f)(long double, int, long) =
        (long double (*)(long double, int, long))(void *)n_scale;
    double (*volatile g)(long double, int) = (double (*)(long double, int))(void *)n_scale;
    double bits = g(1.5L, 1);
    unsigned long u;
    memcpy(&u, &bits, 8);
    return f(2.0L / 3, 2, 99) + (u >> 40);
}

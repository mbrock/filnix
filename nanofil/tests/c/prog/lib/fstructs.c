/* The clang side of fstructs.c. */
#include <stdarg.h>
#include "fstructs.h"

struct f1 c_f1(float x) { struct f1 s = { x }; return s; }
struct f2 c_f2(float x) { struct f2 s = { x, x + 0.5f }; return s; }
struct f3 c_f3(float x) { struct f3 s = { x, x * 2, x * 3 }; return s; }
struct d1 c_d1(double x) { struct d1 s = { x * 4 }; return s; }
struct d2 c_d2(double x) { struct d2 s = { x, x / 8 }; return s; }
struct ld c_ld(long n, double x) { struct ld s = { n, x }; return s; }
struct dl c_dl(long n, double x) { struct dl s = { x, n }; return s; }
struct dp c_dp(char *p, double x) { struct dp s = { x, p + 1 }; return s; }
struct pd c_pd(char *p, double x) { struct pd s = { p + 2, x }; return s; }
struct fi c_fi(float x, int n) { struct fi s = { x, n }; return s; }
struct df c_df(double x) { struct df s = { x, (float)x / 2 }; return s; }
double c_take(struct f1 a, struct f2 b, struct f3 c, struct d2 e,
              struct dl g, struct dp h, struct pd i, struct fi j, struct df k)
{
    return a.a + b.a * 2 + b.b * 3 + c.a + c.b * 5 + c.c * 7 + e.a * 11 + e.b
         + g.a + g.b * 17 + h.a + *h.p + *i.p * 19 + i.a + j.a + j.b * 23 + k.a + k.b * 29;
}
double c_vtake(int n, ...)
{
    va_list ap;
    va_start(ap, n);
    struct f2 b = va_arg(ap, struct f2);
    struct dp h = va_arg(ap, struct dp);
    struct df k = va_arg(ap, struct df);
    double t = va_arg(ap, double);
    va_end(ap);
    return n + b.a + b.b * 3 + h.a + *h.p * 5 + k.a + k.b * 7 + t;
}

double c_calls_back(char *buf)
{
    struct f1 a = n_f1(1.5f); struct f2 b = n_f2(2.5f); struct f3 c = n_f3(3.5f);
    struct d1 d = n_d1(4.5); struct d2 e = n_d2(5.5); struct ld f = n_ld(6, 6.5);
    struct dl g = n_dl(7, 7.5); struct dp h = n_dp(buf, 8.5); struct pd i = n_pd(buf, 9.5);
    struct fi j = n_fi(10.5f, 10); struct df k = n_df(11.5);
    struct dp (*volatile fp)(char *, double) = n_dp;
    struct f3 (*volatile f3p)(float) = n_f3;
    struct dp h2 = fp(buf, 1.25);
    struct f3 c2 = f3p(0.25f);
    return n_take(a, b, c, e, g, h, i, j, k) + h2.a + *h2.p + c2.c
         + n_vtake(2, b, h, k, 0.125);
}

/* Wrong prototypes: an extra argument, and fewer result words. */
double c_generic(char *buf)
{
    struct d2 (*volatile f)(double, long) = (struct d2 (*)(double, long))(void *)n_d2;
    struct dp (*volatile g)(char *, double, long) = (struct dp (*)(char *, double, long))(void *)n_dp;
    double (*volatile h)(double) = (double (*)(double))(void *)n_d2;
    struct d2 e = f(3.0, 0);
    struct dp p = g(buf, 2.0, 0);
    return e.a + e.b + p.a + *p.p + h(16.0);
}

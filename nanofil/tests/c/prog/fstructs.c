// link: lib/fstructs.c
// signatures
/* Structs with float members by value across the nanofil/clang
   boundary: SSE eightbytes, mixed INTEGER/SSE ones, and pointers next
   to doubles. The last line reads past a buffer through a pointer that
   came back beside a double, so its capability survived: both builds
   trap there. */
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include "lib/fstructs.h"

struct f1 n_f1(float x) { struct f1 s = { x * 3 }; return s; }
struct f2 n_f2(float x) { struct f2 s = { x - 1, x + 1 }; return s; }
struct f3 n_f3(float x) { struct f3 s = { x, x / 2, x * 4 }; return s; }
struct d1 n_d1(double x) { struct d1 s = { -x }; return s; }
struct d2 n_d2(double x) { struct d2 s = { x * x, x + 0.25 }; return s; }
struct ld n_ld(long n, double x) { struct ld s = { n * 2, x * 3 }; return s; }
struct dl n_dl(long n, double x) { struct dl s = { x * 5, n + 7 }; return s; }
struct dp n_dp(char *p, double x) { struct dp s = { x + 1, p + 3 }; return s; }
struct pd n_pd(char *p, double x) { struct pd s = { p + 4, x - 1 }; return s; }
struct fi n_fi(float x, int n) { struct fi s = { x * 2, n - 1 }; return s; }
struct df n_df(double x) { struct df s = { x / 4, (float)x * 3 }; return s; }
double n_take(struct f1 a, struct f2 b, struct f3 c, struct d2 e,
              struct dl g, struct dp h, struct pd i, struct fi j, struct df k)
{
    return a.a * 3 + b.a + b.b * 2 + c.a * 5 + c.b + c.c * 3 + e.a + e.b * 11
         + g.a * 17 + g.b + h.a * 19 + *h.p + *i.p + i.a * 23 + j.a * 29 + j.b + k.a + k.b * 31;
}
double n_vtake(int n, ...)
{
    va_list ap;
    va_start(ap, n);
    struct f2 b = va_arg(ap, struct f2);
    struct dp h = va_arg(ap, struct dp);
    struct df k = va_arg(ap, struct df);
    double t = va_arg(ap, double);
    va_end(ap);
    return n * 2 + b.a * 3 + b.b + h.a * 5 + *h.p + k.a * 7 + k.b + t;
}

int main(void)
{
    char *buf = calloc(16, 1);
    for (int i = 0; i < 15; i++)
        buf[i] = 'a' + i;
    struct f1 a = c_f1(1.5f); struct f2 b = c_f2(2.5f); struct f3 c = c_f3(3.5f);
    struct d1 d = c_d1(4.5); struct d2 e = c_d2(5.5); struct ld f = c_ld(6, 6.5);
    struct dl g = c_dl(7, 7.5); struct dp h = c_dp(buf, 8.5); struct pd i = c_pd(buf, 9.5);
    struct fi j = c_fi(10.5f, 10); struct df k = c_df(11.5);
    printf("c %g %g %g %g %g %g %g %g %g %g %g %g\n", a.a, b.a, b.b, c.a, c.b, c.c, d.a, e.a, e.b, f.b, g.a, k.b);
    printf("c %ld %ld %g %c %c %g %g %d %g\n", f.a, g.b, h.a, *h.p, *i.p, i.a, j.a, j.b, k.a);
    printf("take %g %g\n", c_take(a, b, c, e, g, h, i, j, k), n_take(a, b, c, e, g, h, i, j, k));
    struct f3 nc = n_f3(1.0f); struct dp nh = n_dp(buf, 2.0); struct pd ni = n_pd(buf, 3.0);
    printf("n %g %g %g %g %c %c %g\n", nc.a, nc.b, nc.c, nh.a, *nh.p, *ni.p, ni.a);
    printf("vtake %g %g\n", c_vtake(3, b, h, k, 0.5), n_vtake(3, b, h, k, 0.5));

    struct dp (*volatile fp)(char *, double) = c_dp;
    struct f2 (*volatile f2p)(float) = c_f2;
    double (*volatile tp)(struct f1, struct f2, struct f3, struct d2,
                          struct dl, struct dp, struct pd, struct fi, struct df) = c_take;
    struct dp h2 = fp(buf, 0.75);
    struct f2 b2 = f2p(0.5f);
    printf("indirect %g %c %g %g %g\n", h2.a, *h2.p, b2.a, b2.b, tp(a, b, c, e, g, h, i, j, k));

    struct d2 (*volatile w)(double, long) = (struct d2 (*)(double, long))(void *)c_d2;
    double (*volatile w2)(double) = (double (*)(double))(void *)c_d2;
    struct d2 e2 = w(2.0, 0);
    printf("generic %g %g %g\n", e2.a, e2.b, w2(3.0));
    printf("calls back %g\n", c_calls_back(buf));
    printf("generic back %g\n", c_generic(buf));
    fflush(stdout);
    struct dp far = c_dp(buf, 0);
    printf("past end %c\n", far.p[15]);
    return 0;
}

/* A struct over 16 bytes is returned through sret, which keeps a fast
   entry; only its argument forces the generic convention. */
struct big { double a, b, c; };
struct big n_big(double x) { struct big s = { x, x, x }; return s; }

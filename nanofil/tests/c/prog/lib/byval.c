/* The clang side of byval.c: byval arguments in both directions,
   through function pointers, variadic calls and wrong prototypes. */
#include <stdarg.h>
#include "byval.h"

long c_trio(long x, struct trio t, long y) { return x + t.a * 10 + *t.p + t.c * 100 + y; }
int c_text(struct text s) { return s.x[0] + s.x[16] * 2; }
long c_mix(struct mix m, struct mix *q, int n) { return m.i + m.j * 2 + m.k * 3 + *m.p + (long)m.v + q->j + n; }
long c_wide(struct wide w)
{
    long s = 0;
    for (int i = 0; i < 6; i++)
        s += *w.p[i] * w.n[i];
    return s;
}
long c_tight(struct tight t) { return t.c + t.n; }
long c_vsum(int n, ...)
{
    va_list ap;
    long s = 0;
    va_start(ap, n);
    for (int i = 0; i < n; i++) {
        struct trio t = va_arg(ap, struct trio);
        s += t.a + *t.p + t.c + va_arg(ap, long);
    }
    va_end(ap);
    return s;
}
struct trio c_mk(struct trio t, long d) { t.a += d; t.p += 1; t.c -= d; return t; }
struct reals c_reals(struct reals r, double k) { r.d[0] *= k; r.d[2] += k; r.f -= 1; return r; }
long c_huge(struct huge h, long k) { return h.a[0] + h.a[39] * 3 + *h.p + k + n_huge(h, k + 1); }

long c_calls_back(char *buf)
{
    struct trio t = { 3, buf + 2, 4 };
    struct text s = { "ABCDEFGHIJKLMNOPQ" };
    struct mix m = { 1, 2, 3, buf + 3, 4.5f };
    struct wide w = { { buf, buf + 1, buf + 2, buf + 3, buf + 4, buf + 5 }, { 1, 2, 3, 4, 5, 6 } };
    struct tight g = { 7, 8 };
    long (*volatile f)(long, struct trio, long) = n_trio;
    struct trio (*volatile k)(struct trio, long) = n_mk;
    struct trio r = k(t, 5);
    struct reals x = { { 1.5, 2.5, 3.5 }, 4.5f };
    struct reals y = n_reals(x, 2);
    return n_trio(1, t, 2) + n_text(s) + n_mix(m, &m, 9) + n_wide(w) + n_tight(g)
         + f(5, t, 6) * 3 + r.a + *r.p + r.c + n_mk(t, 1).a
         + (long)(y.d[0] * 10 + y.d[1] * 100 + y.d[2] * 1000 + y.f * 10000);
}

/* Wrong prototypes: an extra argument, and too few result words. */
long c_generic(char *buf)
{
    struct trio t = { 6, buf + 4, 7 };
    long (*volatile f)(long, struct trio, long, long) =
        (long (*)(long, struct trio, long, long))(void *)n_trio;
    int (*volatile g)(struct text, long) = (int (*)(struct text, long))(void *)n_text;
    struct text s = { "abcdefghijklmnopq" };
    return f(1, t, 2, 99) + g(s, 0);
}

/* byval.c declares this with an extra argument. */
long c_trio_wide(long x, struct trio t, long y) { return x * 2 + t.a + *t.p + y; }

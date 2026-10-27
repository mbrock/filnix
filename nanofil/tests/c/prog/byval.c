// link: lib/byval.c
/* Structs larger than 16 bytes by value across the nanofil/clang
   boundary: this file is built by nanofil and lib/byval.c by clang
   (progtest.sh). Both pass them byval, in the generic convention. The
   last line reads past a buffer through a pointer that went in a byval
   struct and came back, so its capability must have survived: both
   builds trap there. */
#include <stdio.h>
#include <stdlib.h>
#include "lib/byval.h"

/* Declared with one argument more than lib/byval.c defines it with. */
long c_trio_wide(long x, struct trio t, long y, long extra);

long n_trio(long x, struct trio t, long y) { return x + t.a * 7 + *t.p + t.c * 11 + y; }
int n_text(struct text s) { s.x[0] = 'z'; return s.x[0] + s.x[16] * 3; }
long n_mix(struct mix m, struct mix *q, int n) { return m.i + m.j * 5 + m.k + *m.p + (long)(m.v * 2) + q->k + n; }
long n_wide(struct wide w)
{
    long s = 0;
    for (int i = 0; i < 6; i++)
        s += *w.p[i] * (w.n[i] + 1);
    return s;
}
long n_tight(struct tight t) { return t.c * 3 + t.n; }
struct trio n_mk(struct trio t, long d) { t.a *= d; t.p += 2; t.c += d; return t; }
struct reals n_reals(struct reals r, double k) { r.d[1] -= k; r.d[2] *= k; r.f += 2; return r; }
static long n_vsum(int n, ...);

int main(void)
{
    char *buf = calloc(16, 1);
    for (int i = 0; i < 15; i++)
        buf[i] = 'a' + i;
    struct trio t = { 5, buf + 1, 6 };
    struct text s;
    for (int i = 0; i < 17; i++)
        s.x[i] = 'A' + i;
    struct mix m = { 1, 2, 3, buf + 5, 2.5f };
    struct wide w = { { buf, buf + 2, buf + 4, buf + 6, buf + 8, buf + 10 }, { 6, 5, 4, 3, 2, 1 } };
    struct tight g = { 2, 40 };

    printf("c %ld %d %ld %ld %ld\n", c_trio(1, t, 2), c_text(s), c_mix(m, &m, 3), c_wide(w), c_tight(g));
    printf("n %ld %d %ld %ld %ld\n", n_trio(1, t, 2), n_text(s), n_mix(m, &m, 3), n_wide(w), n_tight(g));
    printf("s unchanged %c\n", s.x[0]);
    struct trio r = c_mk(t, 3), q = n_mk(t, 3);
    printf("mk %ld %c %ld %ld %c %ld\n", r.a, *r.p, r.c, q.a, *q.p, q.c);

    struct reals x = { { 0.25, 0.5, 0.75 }, 1.25f };
    struct reals xc = c_reals(x, 4), xn = n_reals(x, 4);
    printf("reals %g %g %g %g %g %g %g %g\n", xc.d[0], xc.d[1], xc.d[2], xc.f, xn.d[0], xn.d[1], xn.d[2], xn.f);

    long (*volatile f)(long, struct trio, long) = c_trio;
    long (*volatile h)(long, struct trio, long) = n_trio;
    struct trio (*volatile k)(struct trio, long) = c_mk;
    printf("indirect %ld %ld %ld\n", f(2, t, 3), h(2, t, 3), k(t, 1).a);

    long (*volatile f2)(long, struct trio, long, long) =
        (long (*)(long, struct trio, long, long))(void *)c_trio;
    printf("generic %ld %ld\n", f2(4, t, 5, 0), c_trio_wide(4, t, 5, 0));

    struct trio u = { 1, buf + 9, 2 };
    printf("variadic %ld %ld\n", c_vsum(2, t, 10L, u, 20L), n_vsum(2, t, u));
    printf("calls back %ld\n", c_calls_back(buf));
    printf("generic back %ld\n", c_generic(buf));
    fflush(stdout);
    r = c_mk(t, 0);
    struct trio e = { 0, r.p + 14, 0 };
    printf("past end %ld\n", c_trio(0, e, 0));
    return 0;
}

static long n_vsum(int n, ...)
{
    struct trio (*volatile id)(struct trio, long) = n_mk;
    (void)id;
    return n + c_vsum(n, (struct trio){ 1, "x", 2 }, 3L, (struct trio){ 4, "y", 5 }, 6L);
}

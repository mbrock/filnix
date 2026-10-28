/* The clang side of aligned.c. */
#include <stdarg.h>
#include "aligned.h"
struct a16 c_a16(struct a16 a, int k) {
    struct a16 r = n_a16(a, k);
    r.x = r.x * 10 + k;
    return r;
}
long c_outer_sum(struct outer o) {
    return o.c + o.u.u8[19] + o.u.u32[0] + o.s + n_outer_sum(o) * 1000;
}
struct pa c_pa(struct pa p) { p.a += 1; p.b *= 2; return p; }
struct ub c_ub(struct ub u, int k) { struct ub r = n_ub(u, k); r.a = r.a * 10 + k; return r; }
long c_lo(struct lo l, int k) { return l.b * 100 + n_lo(l, k); }
long c_va(int n, ...) {
    va_list ap;
    va_start(ap, n);
    struct a16 a = va_arg(ap, struct a16);
    struct ub u = va_arg(ap, struct ub);
    long z = va_arg(ap, long);
    va_end(ap);
    struct a16 b = { 5 };
    struct ub v = { 6 };
    return a.x * 10000 + u.a * 100 + z + 1000000 * n_va(n, b, v, 7L);
}

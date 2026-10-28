// link: lib/aligned.c
/* GNU aligned(N) on struct and union definitions: layout, object
   alignment (globals, locals, arrays, heap), and by-value passing to
   and from clang (lib/aligned.c). */
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "lib/aligned.h"
struct a16 n_a16(struct a16 a, int k) { a.x += k; return a; }
long n_outer_sum(struct outer o) { return o.c + o.u.u8[0] + o.s; }
struct ub n_ub(struct ub u, int k) { u.a -= k; return u; }
long n_lo(struct lo l, int k) { return l.b + k; }
long n_va(int n, ...) {
    va_list ap;
    va_start(ap, n);
    struct a16 a = va_arg(ap, struct a16);
    struct ub u = va_arg(ap, struct ub);
    long z = va_arg(ap, long);
    va_end(ap);
    return a.x * 100 + u.a * 10 + z + n;
}
static union buf g_buf;
struct a16 g_arr[3];
int main(void) {
    printf("a16 %zu %zu\n", sizeof(struct a16), _Alignof(struct a16));
    printf("buf %zu %zu\n", sizeof(union buf), _Alignof(union buf));
    printf("outer %zu %zu u@%zu s@%zu\n", sizeof(struct outer),
           _Alignof(struct outer), offsetof(struct outer, u),
           offsetof(struct outer, s));
    printf("pa %zu %zu b@%zu\n", sizeof(struct pa), _Alignof(struct pa),
           offsetof(struct pa, b));
    printf("bare %zu %zu\n", sizeof(struct bare), _Alignof(struct bare));
    char pad = 1;
    union buf l_buf;
    struct a16 l_arr[3];
    struct outer *h = malloc(2 * sizeof *h);
    printf("aligned %d %d %d %d %d %d\n", (int)((uintptr_t)&g_buf % 16),
           (int)((uintptr_t)&g_arr[1] % 16), (int)((uintptr_t)&l_buf % 16),
           (int)((uintptr_t)&l_arr[2] % 16), (int)((uintptr_t)&h[1].u % 16),
           pad);
    for (int i = 0; i < 20; i++) l_buf.u8[i] = (uint8_t)(i * 7);
    g_buf = l_buf;
    printf("copy %d %u\n", g_buf.u8[19], g_buf.u32[4]);
    struct a16 a = { 3 };
    struct a16 r = c_a16(a, 4);
    printf("a16 call %d\n", r.x);
    struct outer o = { 5, { { 0 } }, -2 };
    o.u.u8[0] = 9;
    o.u.u8[19] = 11;
    h[1] = o;
    printf("outer call %ld %ld\n", c_outer_sum(h[1]), n_outer_sum(o));
    struct pa p = { 'a', 1 << 20 };
    struct pa q = c_pa(p);
    printf("pa call %c %d\n", q.a, q.b);
    struct ub u = { 1000 };
    printf("ub call %ld\n", c_ub(u, 6).a);
    struct lo l = { .b = 7 };
    printf("lo call %ld\n", c_lo(l, 2));
    printf("va call %ld %ld\n", c_va(1, a, u, 3L), n_va(2, a, u, 3L));
    free(h);
    return 0;
}

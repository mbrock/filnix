/* _Atomic structs and unions of at most 8 bytes (bind's
   _Atomic(isc_time_t)): clang rounds the size up to a power of two P and
   aligns to it, and every load, store, exchange and compare-exchange is
   one P-byte access, a store writing the padding as zero. A
   compare-exchange is only of a struct already of its atomic size
   (reject/atomic-struct-cas.c). */
#include <stdatomic.h>
#include <stdio.h>
#include <string.h>

typedef struct { unsigned s, ns; } t8;          /* aligned 4, atomic 8 */
typedef struct { char a, b, c; } t3;            /* 3 bytes, atomic 4 */
typedef struct { char a[5]; } t5;               /* 5 bytes, atomic 8 */
typedef struct { short a; char b; } t3b;        /* inner padding */
typedef struct { char c; } t1;
typedef union { int i; float f; } u4;
typedef struct { float x, y; } f2;

struct holder { char pad; _Atomic(t3) x; char after; _Atomic(t5) y; _Atomic t1 z; };
_Atomic(t8) g = (t8){1, 2};
static _Atomic(t3) arr[4];
static struct holder sh = {7, (t3){1, 2, 3}, 9, (t5){{4, 5, 6, 7, 8}}, (t1){10}};
volatile _Atomic(f2) vf;

static void bytes(const void *p, int n) {
    const unsigned char *b = p;
    for (int i = 0; i < n; i++) printf("%d ", b[i]);
    printf("\n");
}
static t3 make3(int a) { t3 r = {(char)a, (char)(a + 1), (char)(a + 2)}; return r; }
static int sum3(t3 v) { return v.a + v.b + v.c; }
/* nanofil's own static functions take a struct holding one by value
   (returning one is refused: reject/atomic-struct-return.c) */
struct w3 { _Atomic(t3) v; int k; };
static void bump(struct w3 w, struct w3 *out) { t3 v = w.v; v.c++; out->v = v; out->k = w.k + 1; }
typedef _Atomic t3 at3q;                        /* the qualifier spelling */
struct q3 { _Atomic t3 x; int k; };

int main(void) {
    printf("%zu %zu | %zu %zu | %zu %zu | %zu %zu | %zu %zu\n",
           sizeof(_Atomic(t8)), _Alignof(_Atomic(t8)), sizeof(_Atomic(t3)), _Alignof(_Atomic(t3)),
           sizeof(_Atomic(t5)), _Alignof(_Atomic(t5)), sizeof(_Atomic(u4)), _Alignof(_Atomic(t3b)),
           sizeof(struct holder), __builtin_offsetof(struct holder, y));
    printf("%zu %zu\n", __builtin_offsetof(struct holder, after), __builtin_offsetof(struct holder, z));
    t8 a = g;
    printf("%u %u\n", a.s, a.ns);
    g = (t8){3, 4};
    a = atomic_load(&g);
    printf("%u %u\n", a.s, a.ns);
    atomic_store_explicit(&g, ((t8){5, 6}), memory_order_release);
    t8 old = atomic_exchange(&g, ((t8){7, 8}));
    printf("%u %u\n", old.s, old.ns);
    t8 exp = {7, 8};
    _Bool ok = atomic_compare_exchange_strong(&g, &exp, ((t8){9, 10}));
    printf("%d %u %u\n", ok, exp.s, exp.ns);
    exp = (t8){1, 1};
    ok = atomic_compare_exchange_weak_explicit(&g, &exp, ((t8){11, 12}), memory_order_acq_rel, memory_order_acquire);
    printf("%d %u %u\n", ok, exp.s, exp.ns);

    /* arrays, pointers and padding */
    memset(arr, 0x55, sizeof arr);
    for (int i = 0; i < 4; i++) arr[i] = make3(10 * i);
    bytes(arr, sizeof arr);
    _Atomic(t3) *p = &arr[2];
    t3 v = *p;
    printf("%d %d\n", sum3(v), sum3(arr[3]));
    *p = make3(100);
    t3 o3 = atomic_exchange(&arr[1], make3(50));
    printf("%d %d %d\n", sum3(*p), sum3(o3), sum3(atomic_load(&arr[1])));
    /* compare-exchange of a struct already of its atomic size */
    _Atomic(t3b) cb;
    t3b b0 = {1, 2}, b1 = {3, 4}, be = {1, 2};
    memset(&cb, 0, sizeof cb);
    cb = b0;
    ok = atomic_compare_exchange_strong(&cb, &be, b1);
    printf("%d %d %d\n", ok, ((t3b)cb).a, be.b);
    be = (t3b){9, 9};
    ok = atomic_compare_exchange_strong(&cb, &be, b0);
    printf("%d %d %d\n", ok, be.a, be.b);

    /* members of a struct holding atomic ones, and copies of it */
    struct holder h;
    memset(&h, 0x55, sizeof h);
    h.x = make3(1);
    h.y = sh.y;
    h.z = (t1){3};
    bytes(&h, sizeof h);
    struct holder h2 = sh;
    t5 y = h2.y;
    printf("%d %d %d %d %d\n", h2.pad, sum3(h2.x), h2.after, y.a[4], ((t1)h2.z).c);
    _Atomic(t3) local = make3(30), local2 = local;
    printf("%d %d\n", sum3(local), sum3(local2));

    /* unions, floats, inner padding, conditionals */
    _Atomic(u4) u;
    atomic_init(&u, ((u4){.f = 1.5f}));
    u4 uu = u;
    printf("%x\n", uu.i);
    vf = (f2){0.25f, -2.0f};
    f2 fv = vf;
    printf("%g %g\n", fv.x, fv.y);
    _Atomic(t3b) tb;
    t3b in;
    memset(&in, 0x77, sizeof in);
    in.a = 300; in.b = 4;
    tb = in;
    bytes(&tb, sizeof tb);
    t3 c = sum3(v) > 0 ? arr[2] : make3(0);
    printf("%d\n", sum3(c));
    struct w3 w;
    w.v = make3(5); w.k = 1;
    bump(w, &w);
    bump(w, &w);
    printf("%d %d\n", sum3(w.v), w.k);

    /* _Atomic as a qualifier on a typedef or typeof name */
    at3q qa; _Atomic typeof(v) qc; volatile _Atomic t3 qg; t3 _Atomic qh; at3q qi[2];
    printf("%zu %zu %zu %zu %zu %zu\n", sizeof qa, sizeof qc, sizeof qg, sizeof qh, sizeof qi, sizeof(typeof(qa)));
    _Alignas(4) unsigned char buf[4] = {0x55, 0x55, 0x55, 0x55};
    _Atomic t3 *qp = (void *)buf;
    *qp = make3(1);
    bytes(buf, 4);
    struct q3 qs;
    memset(&qs, 0x55, sizeof qs);
    qs.x = make3(4);
    bytes(&qs, sizeof qs);
    printf("%d %zu\n", _Generic(&arr[0], _Atomic t3 *: 1, default: 2), sizeof(qh = v));
    return 0;
}

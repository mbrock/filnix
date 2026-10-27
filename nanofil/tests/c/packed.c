/* GNU packed structs and unions (cproc struct-packed): members at
   alignment 1, struct alignment 1, misaligned loads and stores, copies,
   static initializers, arrays of them, the attribute before the tag,
   after the body and as [[gnu::packed]], and a misaligned struct
   returned in memory (SysV class MEMORY). */
#include <stddef.h>
struct [[gnu::packed]] P { char a; long long b; short c; };
typedef struct { char t; int u; } __attribute__((__packed__)) T;
union __attribute__((packed)) U { short s; char b[3]; };
struct Outer { char x; T t; struct P p; };
static struct P gp = { 1, 0x0102030405060708LL, -3 };
static T gts[3] = { { 1, 2 }, { 3, 4 }, { 5, 6 } };

long layout(long x) {
    return sizeof(struct P) * 1000000 + offsetof(struct P, c) * 10000
           + sizeof(T) * 1000 + _Alignof(T) * 100 + sizeof(union U) * 10
           + offsetof(struct Outer, p) + x * 0;
}
long access(long x) {
    struct P p = { 2, x, 7 };
    p.b += 1;
    p.c = (short)(p.c * 3);
    T ts[2];
    ts[1].u = (int)x * 2;
    ts[0] = ts[1];
    struct Outer o = { 1, { 2, 3 }, p };
    return p.b * 1000 + p.c * 10 + ts[0].u + o.p.b * 100000 + o.t.u;
}
long statics(long i) { return gp.b - gp.c + gts[i].u * 1000 + gts[i].t * 100; }
static struct P make(long x) { struct P p = { 9, x, 4 }; return p; }
long returned(long x) { struct P p = make(x); return p.a + p.b * 10 + p.c * 1000; }
long oob(long i) { T ts[2] = { { 1, 2 }, { 3, 4 } }; char *q = (char *)ts; return q[i]; }
// run: $layout 0
// run: $access 5
// run: $statics 2
// run: $returned 6
// run: $oob 9
// run: $oob 16

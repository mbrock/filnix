/* Compound literals (block and file scope), wide character and string
   literals (L, u, U, concatenation, static and automatic initializers),
   GNU c ?: b (c evaluated once) and __builtin_expect. */
#include <wchar.h>
#include <stddef.h>
struct P { int x, y; };
static int sum(const int *p, int n) { int s = 0; for (int i = 0; i < n; i++) s += p[i]; return s; }
static int px(struct P p) { return p.x * 10 + p.y; }
int *gp = (int[]){ 5, 6, 7 };
struct P *gq = &(struct P){ 8, 9 };
wchar_t gw[] = L"h\u00e9\x10000";
long complit(long x) {
    int t = 0;
    for (int i = 0; i < 3; i++) { int *p = (int[]){ i, i + 1 }; p[0] += 10; t += p[0] + p[1]; }
    struct P *q = &(struct P){ .y = (int)x };
    return t * 1000 + sum((int[]){ 1, 2, 3, [5] = 4 }, 6) * 100 + px((struct P){ 1, 2 }) + q->y + gp[2] + gq->y;
}
long complit_oob(long x) { int *p = (int[4]){ 1 }; return p[x]; }
long wide(long x) {
    wchar_t s[] = L"hé€€x";
    const wchar_t *t = L"ab" L"c" "d";
    unsigned short u[] = u"z\u20ac";
    unsigned int U[] = U"\U0001F600";
    return s[x] + sizeof(s) / sizeof(s[0]) * 100000 + t[3] * 1000 + u[1] + U[0] + L'\001' + gw[2] + -L'\001' * 7 + gw[1];
}
long gnu(long x) { int n = 0; long r = (x ? x + n++ : 0) ?: 77; return r * 10 + n + __builtin_expect(x, 1); }
long gnup(long x) { char a[2] = { 3, 4 }; char *p = x ? a : 0; char *q = p ?: a + 1; return *q; }
// run: $complit 4
// run: $complit_oob 3
// run: $complit_oob 16
// run: $wide 1
// run: $wide 4
// run: $gnu 0
// run: $gnu 5
// run: $gnup 0
// run: $gnup 1
/* An operand that && || or ?: does not evaluate may divide by zero
   (C11 6.6p3); the array sizes are still constant. */
long lazy(long x) { static char a[1 || 1/0], b[(0 && 1/0) + 2], c[1 ? 3 : 1/0]; return sizeof a + sizeof b * 10 + sizeof c * 100 + x * 0; }
// run: $lazy 0
/* Parenthesized abstract declarators: an array parameter, and a pointer
   declarator after a GNU attribute (c-testsuite 00209, 00210). */
static long twice(long x) { return 2 * x; }
static long first(long ([2]), long);
static long first(long a[2], long i) { return a[i]; }
long abstract(long x) {
    long a[2] = { x, 7 };
    void *p = twice;
    return first(a, 1) * 100 + ((long (__attribute__((noinline)) *)(long))p)(x);
}
// run: $abstract 4
/* GNU range designators, overlapping and later overridden; a designator
   naming a member of an anonymous member (C11 6.7.2.1p13); and GNU
   constant compound literals in static initializers (c-testsuite 00216). */
struct Q { char a, b; };
union R { struct { char x, y; }; struct Q q; };
static struct Q gq2 = ((struct Q){ 3, 4 });
static struct { struct Q q; char c; } gqc = { (struct Q){ 5, 6 }, 7 };
static int granges[8] = { [1 ... 5] = 9, [4 ... 6] = 2, [2] = 1, 8 };
long ranges(long x) {
    int a[6] = { [0 ... 2] = (int)x, [4 ... 5] = 3 };
    union R r = { .y = 7, .x = 6 };
    long s = 0;
    for (int i = 0; i < 8; i++) s = s * 10 + granges[i];
    return s * 1000000000 + a[0] * 100000 + a[2] * 10000 + a[3] * 1000 + a[5] * 100
           + r.q.a * 10 + r.q.b + gq2.b * 1000000 + gqc.q.b * 10000000 + gqc.c * 100000000L;
}
// run: $ranges 4

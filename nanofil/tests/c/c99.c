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

/* Struct and union values inside one module (M4d): copies, returns in
   one word, two words, a buffer (pointer fields) and sret, arguments
   split into eightbytes, odd sizes, ?: and members of rvalues. */
struct two { long a, b; };
struct pw { char *p; long n; };
struct small { int a; char c; };
struct three { long a, b, c; };
struct mix { int a; int b; char *p; };
struct odd { char a, b, c; };
struct twelve { int a, b, c; };

static struct two mk_two(long x) { struct two t = { x, x + 1 }; return t; }
static struct pw mk_pw(char *p, long n) { struct pw r; r.p = p; r.n = n; return r; }
static struct small mk_small(int x) { struct small s = { x, 'c' }; return s; }
static struct three mk_three(long x) { struct three t = { x, 2 * x, 3 * x }; return t; }
static long sum_mix(struct mix m) { return m.a + m.b + *m.p; }
static struct odd mk_odd(int x) { struct odd o = { x, x + 1, x + 2 }; return o; }
static int sum_odd(struct odd o) { return o.a * 100 + o.b * 10 + o.c; }
static struct twelve bump(struct twelve t) { t.a++; t.c += 5; return t; }

long two(long x) { struct two t = mk_two(x); return t.a * 10 + t.b; }
long pw(long n) { char buf[4] = { 5, 6, 7, 8 }; struct pw r = mk_pw(buf + 1, n); return *r.p + r.n; }
long pw_over(long n) { char buf[4] = { 5, 6, 7, 8 }; struct pw r = mk_pw(buf, n); return r.p[n]; }
long small(long x) { struct small s = mk_small(x); return s.a + s.c; }
long three(long x) { struct three t = mk_three(x); return t.a + t.b + t.c + mk_three(1).c; }
long mix(long x) { char c = 3; struct mix m = { x, 2, &c }; return sum_mix(m); }
long odd(long x) { return sum_odd(mk_odd(x)); }
long twelve(long x) { struct twelve t = { x, 0, 1 }; struct twelve u = bump(t); return u.a * 100 + u.b * 10 + u.c + t.a; }
long copy(long x) { struct pw a = { 0, x }, b; char k = 9; a.p = &k; b = a; a.n = 0; return b.n + *b.p; }
long cond(long x) { struct two a = { 1, 2 }, b = { 3, 4 }; struct two c = x ? a : b; return c.a + c.b * 10; }
long member_rv(long x) { return mk_two(x).b + mk_three(x).c; }
long elems(long x) { struct two a = { x, 1 }, b = { 2, 3 }; struct two ts[2] = { a, b }; struct { struct two t; long k; } w = { b, 4 }; return ts[0].a + ts[1].b * 10 + w.t.a * 100 + w.k * 1000; }
union up { char *p; long n; };
static union up mk_up(char *p) { union up u; u.p = p; return u; }
long up(long x) { char c[2] = { 4, 5 }; union up u = mk_up(c); return u.p[x]; }
long arr(long x) { struct two ts[3] = { { 1, 2 }, { 3, 4 }, { 5, 6 } }; ts[1] = ts[x]; return ts[1].a + ts[1].b; }
// run: $two 4
// run: $pw 3
// run: $pw_over 3
// run: $pw_over 16
// run: $small 7
// run: $three 2
// run: $mix 10
// run: $odd 1
// run: $twelve 3
// run: $copy 5
// run: $cond 0
// run: $cond 1
// run: $member_rv 3
// run: $arr 2
// run: $arr 0
// run: $elems 7
// run: $up 1
// run: $up 16

/* Array lengths from brace-elided initializers, and a designator after an
   elided element (both wrong before: 4 structs instead of 2, and a
   "bad array designator"). */
struct S { int a, b; };
struct S gs[] = { 1, 2, 3, 4 };
struct N { struct S s; char c[3]; };
struct N gn[] = { 1, 2, "ab", { { 3, 4 }, "cd" }, 5, [4] = 9 };
struct N gd[] = { 1, [2] = 9 };
int ga[][2] = { 1, 2, 3, 4, 5 };
long lens(long x) {
    struct S ls[] = { 1, 2, 3, 4, 5 };
    struct S a = { 7, 8 };
    struct S ws[] = { a, a, 1 };
    return sizeof(gs) / sizeof(gs[0]) * 10000 + sizeof(gn) / sizeof(gn[0]) * 1000
         + sizeof(ga) / sizeof(ga[0]) * 100 + sizeof(ls) / sizeof(ls[0]) * 10 + sizeof(ws) / sizeof(ws[0]) + gn[1].c[1] * 0 + x * 0;
}
long vals(long x) { return gs[1].a * 1000 + gn[1].s.b * 100 + gn[1].c[0] + ga[2][0] * 10000 + sizeof(gd) / sizeof(gd[0]) * 100000 + gd[2].s.a * 1000000 + x * 0; }
// run: $lens 0
// run: $vals 0
/* A braced initializer for a slot replaces what earlier designators put
   there, and a designator may name any member of a union. */
union cu { char c; int i; };
struct two go[1] = { [0].a = 1, [0] = { .b = 2 } };
union cu gu = { .i = 0x1234 };
long override(long x) { struct two lo[1] = { [0].a = x, [0] = { .b = 3 } }; union cu lu = { .i = 0x5600 + x }; return go[0].a * 10000 + go[0].b * 1000 + lo[0].a * 100 + lo[0].b * 10 + (gu.i == 0x1234) + (lu.i - 0x5600 == x) * 2; }
// run: $override 7
/* Members of a const struct, in ?: arms and as a whole initializer
   entry (deflate.c's configuration_table[...].func in a ?: chain). */
typedef long (*cfn)(long);
long twice(long x) { return 2 * x; }
const struct cfg { long a; cfn f; } ctab[2] = { { 5, twice }, { 6, twice } };
long cmember(long x) {
    const struct cfg *p = &ctab[1];
    struct cfg w[] = { ctab[0], 7, twice };
    return x ? (*(ctab[x].f))(x) + p->a * 100 : ctab[0].a + sizeof(w) / sizeof(w[0]) * 10;
}
// run: $cmember 0
// run: $cmember 1
/* A struct may be cast to its own type (a GNU extension clang and GCC
   accept). */
struct own { long a, b; };
long own_cast(long x) { struct own o = { x, 2 }; return ((struct own)o).a * 10 + ((struct own)o).b; }
// run: $own_cast 4

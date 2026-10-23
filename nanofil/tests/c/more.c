/* Integer conversions, aggregates and control flow. Each function is run
   by the interpreter, by nanofil's code and by clang (see difftest.sh). */

typedef unsigned char u8;
enum color { RED, GREEN = 5, BLUE };
struct pt { int x, y; };
struct box { struct pt lo, hi; char tag; long area; };
union num { int i; unsigned char b[4]; };

int narrow(int x) {
    signed char c = x;
    u8 u = x;
    short s = x;
    unsigned short us = x;
    c += 100;
    u *= 3;
    return c + u + s + us;
}

long mixed(int a, unsigned b, long c) {
    unsigned long r = a * b;
    r += c / a;
    r ^= (unsigned long)-a;
    return (long)r % 1000 + (a < b) + (-1 < 0u) * 7 + (c > -1);
}

int divs(int a, int b) { return (a / b) * 1000 + (a % b) + (int)((unsigned)a / (unsigned)b % 100); }

int enums(int k) {
    enum color c = k;
    switch (c) {
    case RED: return 1;
    case GREEN:
    case BLUE: return c * 10;
    }
    return sizeof(enum color) + BLUE;
}

int structs(int k) {
    struct box b = { {1, 2}, .hi = {k, 4}, 'z', 0 };
    struct box *p = &b;
    p->area = (long)(p->hi.x - p->lo.x) * (b.hi.y - b.lo.y);
    return (int)p->area + b.tag + sizeof(struct box) + (int)(long)&((struct box *)0)->tag;
}

int unions(int v) {
    union num n;
    n.i = v;
    return n.b[0] + n.b[3] * 1000 + sizeof n;
}

int grid(int r, int c) {
    int g[3][4] = { {1, 2, 3, 4}, {5, 6, 7, 8}, 9, 10 };
    int total = 0;
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 4; j++) {
            if (j > c) break;
            if ((i + j) % 2) continue;
            total += g[i][j];
        }
    }
    return total * 100 + g[r][c] + sizeof g / sizeof g[0];
}

int strings(int i) {
    char s[] = "hello";
    char t[8] = "ab";
    u8 *p = (u8 *)s;
    int n = 0;
    while (*p++) n++;
    return n * 1000 + s[i] + t[5] + sizeof s;
}

int walk(int n) {
    long a[6] = { [2] = 7, [4] = 9, 11 };
    long *p = a, *end = a + 6;
    long s = 0;
    for (; p < end; ++p) s = s * 3 + *p;
    p = &a[5];
    while (p != a && n--) p--;
    return (int)s + (int)(p - a) * 1000000 + (end - a == 6);
}

static int odd(int n);
static int even(int n) { return n == 0 ? 1 : odd(n - 1); }
static int odd(int n) { return n == 0 ? 0 : even(n - 1); }
int parity(int n) { return even(n) * 10 + odd(n); }

int ptrs(int k) {
    int x = 1, y = 2;
    int *p = k ? &x : &y, **pp = &p;
    **pp += 40;
    int *q = 0;
    return x * 100 + y + !q * 1000 + (p ? 5 : 6) + (q == 0) + (*pp == &x) * 10000;
}

int shortcircuit(int a) {
    int calls = 0;
    int r = (a > 2 && ++calls) || (++calls, a == 0);
    r += (a || ++calls) * 10;
    return r * 100 + calls + (a, 4);
}

int oob(int i) { int a[4] = {0}; return a[i]; }

/* nanofil allocates locals with filc_allocate, whose bounds are rounded
   up to 16 bytes, so q[2] and q[3] do not trap yet (clang's do). */
int oobp(int i) { struct pt p = {1, 2}; int *q = &p.x; return q[i]; }

// run: $narrow 0
// run: $narrow 200
// run: $narrow 70000
// run: $narrow 4294967295
// run: $mixed 3 7 100
// run: $mixed 4294967291 3 18446744073709551615
// run: $divs 4294967289 2
// run: $divs 17 5
// run: $enums 0
// run: $enums 5
// run: $enums 6
// run: $enums 9
// run: $structs 7
// run: $unions 305419896
// run: $grid 2 1
// run: $grid 0 3
// run: $strings 1
// run: $strings 5
// run: $walk 2
// run: $walk 100
// run: $parity 7
// run: $parity 10
// run: $ptrs 1
// run: $ptrs 0
// run: $shortcircuit 0
// run: $shortcircuit 1
// run: $shortcircuit 5
// run: $oob 3
// run: $oob 4
// run: $oob 4294967295
// run: $oobp 1
// run: $oobp 4
// run: $oobp 4294967295
/* Any integer constant expression of value 0 is a null pointer constant
   in assignment, arguments, returns and initializers (C11 6.3.2.3p3). */
static int is_null(int *p) { return p == 0; }
static int *null_ret(void) { return 1 - 1; }
long null_constants(long x) {
    int *p = (char)0, *q;
    q = (long)0;
    void (*fp)(void) = 1 ? 0 : 0;
    return is_null(p) + is_null(q) * 2 + is_null(null_ret()) * 4 + (fp == 0) * 8 + is_null(1 - 1) * 16 + x * 0;
}
// run: $null_constants 0

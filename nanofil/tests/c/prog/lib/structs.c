/* The clang side of structs.c: struct arguments and returns in both
   directions, through function pointers, and through pointers of the
   wrong type, which go by way of the generic entries. */
#include "structs.h"

struct two c_two(long x) { struct two t = { x, x * 2 }; return t; }
struct pw c_pw(char *p, long n) { struct pw w = { p + 2, n }; return w; }
struct pp c_pp(char *p) { struct pp r = { p, p + 3 }; return r; }
struct small c_small(int x) { struct small s = { x, 'k' }; return s; }
struct odd c_odd(int x) { struct odd o = { x, x * 2, x * 3 }; return o; }
struct big c_big(char *p, long x) { struct big b = { x, x + 1, p + 4, x + 2 }; return b; }
union up c_up(char *p) { union up u; u.p = p + 5; return u; }
long c_take(struct two t, struct pw w, struct small s, struct odd o)
{
    return t.a + t.b * 10 + *w.p + w.n * 100 + s.a + s.c + o.a + o.b + o.c;
}

/* structs.c declares these with an extra argument. */
struct two c_two_wide(long x) { struct two t = { x + 1, x + 2 }; return t; }
struct pw c_pw_wide(char *p, long n) { struct pw w = { p + 3, n }; return w; }

long c_calls_back(char *buf)
{
    struct two t = n_two(3);
    struct pw w = n_pw(buf, 4);
    struct pp q = n_pp(buf);
    struct small s = n_small(6);
    struct odd o = n_odd(7);
    struct big b = n_big(buf, 8);
    union up u = n_up(buf);
    struct two (*volatile f)(long) = n_two;
    struct pw (*volatile g)(char *, long) = n_pw;
    struct big (*volatile h)(char *, long) = n_big;
    struct two t2 = f(5);
    struct pw w2 = g(buf, 6);
    struct big b2 = h(buf, 1);
    return t.a + t.b + *w.p + w.n + *q.q + s.a + s.c + o.a + o.c + b.a + *b.p + b.c + *u.p
         + t2.a * 3 + *w2.p + w2.n + b2.c + n_take(t, w, s, o);
}

/* Wrong signatures: an extra argument, or fewer result words than the
   callee returns. */
long c_generic(char *buf)
{
    struct two (*volatile f)(long, long) = (struct two (*)(long, long))(void *)n_two;
    struct pw (*volatile g)(char *, long, long) = (struct pw (*)(char *, long, long))(void *)n_pw;
    long (*volatile h)(long) = (long (*)(long))(void *)n_two;
    char *(*volatile k)(char *, long) = (char *(*)(char *, long))(void *)n_pw;
    struct two t = f(4, 0);
    struct pw w = g(buf, 7, 0);
    return t.a + t.b * 10 + *w.p + w.n + h(9) + *k(buf, 0);
}

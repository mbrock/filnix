// link: lib/structs.c
/* Struct values across the nanofil/clang boundary: this file is built by
   nanofil and lib/structs.c by clang (progtest.sh). The last line reads
   past a buffer through a pointer that came back in a struct, so the
   capability must have survived: both builds trap there. */
#include <stdio.h>
#include <stdlib.h>
#include "lib/structs.h"

/* Declared with one argument more than lib/structs.c defines them with,
   so the call goes through the thunk's generic path. */
struct two c_two_wide(long x, long extra);
struct pw c_pw_wide(char *p, long n, long extra);

struct two n_two(long x) { struct two t = { x, -x }; return t; }
struct pw n_pw(char *p, long n) { struct pw r = { p + 1, n }; return r; }
struct pp n_pp(char *p) { struct pp r = { p + 2, p + 3 }; return r; }
struct small n_small(int x) { struct small s = { x, 'n' }; return s; }
struct odd n_odd(int x) { struct odd o = { x, x + 1, x + 2 }; return o; }
struct big n_big(char *p, long x) { struct big b = { x, x * 2, p + 2, x * 3 }; return b; }
union up n_up(char *p) { union up u; u.p = p + 1; return u; }
long n_take(struct two t, struct pw w, struct small s, struct odd o)
{
    return t.a * 2 + t.b + *w.p + w.n + s.a * 3 + s.c + o.a * 5 + o.b + o.c;
}

int main(void)
{
    char *buf = calloc(16, 1);
    for (int i = 0; i < 15; i++)
        buf[i] = 'a' + i;
    struct two t = c_two(5);
    struct pw w = c_pw(buf, 3);
    struct pp q = c_pp(buf);
    struct small s = c_small(9);
    struct odd o = c_odd(2);
    struct big b = c_big(buf, 10);
    union up u = c_up(buf);
    printf("two %ld %ld\n", t.a, t.b);
    printf("pw %c %ld\n", *w.p, w.n);
    printf("pp %c %c\n", *q.p, *q.q);
    printf("small %d %c\n", s.a, s.c);
    printf("odd %d %d %d\n", o.a, o.b, o.c);
    printf("big %ld %ld %c %ld\n", b.a, b.b, *b.p, b.c);
    printf("up %c\n", *u.p);
    printf("c_take %ld\n", c_take(t, w, s, o));
    printf("n_take %ld\n", n_take(t, w, s, o));

    struct two (*volatile f)(long) = c_two;
    struct pw (*volatile g)(char *, long) = c_pw;
    struct big (*volatile h)(char *, long) = c_big;
    t = f(6);
    w = g(buf, 4);
    b = h(buf, 1);
    printf("indirect %ld %ld %c %ld %c %ld\n", t.a, t.b, *w.p, w.n, *b.p, b.c);

    struct two (*volatile f2)(long, long) = (struct two (*)(long, long))(void *)c_two;
    struct pw (*volatile g2)(char *, long, long) = (struct pw (*)(char *, long, long))(void *)c_pw;
    long (*volatile h2)(long) = (long (*)(long))(void *)c_two;
    t = f2(7, 0);
    w = g2(buf, 5, 0);
    printf("generic %ld %ld %c %ld %ld\n", t.a, t.b, *w.p, w.n, h2(8));

    t = c_two_wide(3, 0);
    w = c_pw_wide(buf, 6, 0);
    printf("wide %ld %ld %c %ld\n", t.a, t.b, *w.p, w.n);

    printf("calls back %ld\n", c_calls_back(buf));
    printf("generic back %ld\n", c_generic(buf));
    fflush(stdout);
    w = c_pw(buf, 0);
    printf("past end %c\n", w.p[14]);
    return 0;
}

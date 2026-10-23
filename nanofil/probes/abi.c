#include <stddef.h>
#include <string.h>
struct small { long a, b; };
struct big { long a, b, c; };
struct withptr { char *p; long n; };
void f0(void) {}
long add2(long a, long b) { return a + b; }
size_t mylen(const char *s) { return strlen(s); }
char *pick(char *a, char *b, char *c, long i) { return i ? a : (i > 1 ? b : c); }
/* 3 pointer args = 6 GPRs + thread + lower = 8 > 6 regs */
long sum_loop(long *p, long n) { long s = 0; for (long i = 0; i < n; i++) s += p[i]; return s; }
struct small ret_small(long x) { struct small s = { x, x + 1 }; return s; }
struct big ret_big(long x) { struct big s = { x, x + 1, x + 2 }; return s; }
long take_small(struct small s) { return s.a + s.b; }
long take_big(struct big s) { return s.a + s.c; }
long take_withptr(struct withptr w) { return w.p[w.n]; }
struct withptr ret_withptr(char *p) { struct withptr w = { p, 3 }; return w; }
const char *lit(void) { return "hello"; }
extern char *ext(char *, char *, char *, char *);
char *callext(char *a) { return ext(a, a, a, a); }

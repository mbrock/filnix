#include <stdarg.h>
/* Structs of 16 bytes or less with float members (SSE and mixed
   eightbytes), and aggregate va_arg, inside one module. */
struct f1 { float a; };
struct f2 { float a, b; };
struct f3 { float a, b, c; };
struct d2 { double a, b; };
struct mix { long a; double b; };
struct dl { double a; long b; };
struct dp { double a; char *p; };
struct fi { float a; int b; };
struct df { double a; float b; };
union uf { float f; double d; };
static struct f1 m1(float x) { struct f1 s = { x }; return s; }
static struct f2 m2(float x) { struct f2 s = { x, x * 2 }; return s; }
static struct f3 m3(float x) { struct f3 s = { x, x * 2, x * 3 }; return s; }
static struct d2 md2(double x) { struct d2 s = { x, x / 4 }; return s; }
static struct mix mmix(long n, double x) { struct mix s = { n, x }; return s; }
static struct dl mdl(long n, double x) { struct dl s = { x, n }; return s; }
static struct dp mdp(char *p, double x) { struct dp s = { x, p + 1 }; return s; }
static struct fi mfi(float x, int n) { struct fi s = { x, n }; return s; }
static struct df mdf(double x) { struct df s = { x, (float)x * 3 }; return s; }
static double t(struct f1 a, struct f2 b, struct f3 c, struct d2 d, struct mix e, struct dl f, struct dp g, struct fi h, struct df i, union uf u)
{ return a.a + b.a * 2 + b.b + c.a + c.c * 5 + d.a + d.b * 3 + e.a + e.b + f.a + f.b * 7 + g.a + *g.p + h.a + h.b + i.a + i.b + u.d; }
long floats(long k)
{
    char buf[3] = { 1, 2, 3 };
    union uf u; u.d = 0.5 * k;
    double r = t(m1(k), m2(k + 1), m3(k + 2), md2(k), mmix(k, 1.5), mdl(k, 2.5), mdp(buf, 3.25), mfi(k, 4), mdf(k), u);
    struct dp g = mdp(buf, 1);
    return (long)(r * 100) + g.p[k];
}
// run: $floats 0
// run: $floats 1
// run: $floats 2

struct s7 { char x[7]; };
struct pw { char *p; long n; };
struct big { long a; char *p; long c; };
static long v(int n, ...) { va_list ap; va_start(ap, n); long r = 0;
  struct s7 a = va_arg(ap, struct s7); struct pw b = va_arg(ap, struct pw); struct big c = va_arg(ap, struct big);
  r = a.x[0] + a.x[6] * 10 + *b.p + b.n * 100 + c.a + *c.p + c.c * 1000 + va_arg(ap, long) * 7; va_end(ap); return r; }
long vargs(long k) { char buf[4] = { 1, 2, 3, 4 }; struct s7 a = { { 1, 2, 3, 4, 5, 6, 7 } }; struct pw b = { buf + k, 5 }; struct big c = { 9, buf + 1, 2 };
  return v(0, a, b, c, k); }
// run: $vargs 1
// run: $vargs 3
// run: $vargs 4

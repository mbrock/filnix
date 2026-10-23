#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

float nfloat(void *, float);
double ndouble(void *, double);
double ncall(void *);
double nwide(long, int *, double, double, double, double, double, double,
             double, double, double, long, long, long, long);
double ncallwide(int *);
double nindirect(int *);
double nvar(double, int, ...);
double ncallvar(int *);
double nconsume(va_list);
double nforward(int, ...);
int nfloatbits(void *);
int nshort(int, ...);
float nidentity(float);
int nforge(void *);
double nphi(void *, int);
struct pair { long n; int *p; };
struct pair nbuffer(double, int *, long, int *, double);
long ncallbuffer(int *);
double ndata(void);

void churn(void) { zgc_request_and_wait(); }
float cfloat(void *p, float x) { return nfloat(p, x) + 1.0f; }
double cdouble(double x, void *p) { return ndouble(p, x) + 1.0; }
double cwide(long i, int *p, double a, double b, double c, double d,
             double e, double f, double g, double h, double j,
             long k, long l, long m, long n) {
    return nwide(i, p, a, b, c, d, e, f, g, h, j, k, l, m, n);
}
double cvar(int n, ...) {
    va_list ap;
    va_start(ap, n);
    double a = va_arg(ap, double), b = va_arg(ap, double);
    int *p = va_arg(ap, int *);
    va_end(ap);
    return a + b + *p;
}
double cconsume(va_list ap) { return va_arg(ap, double); }
struct pair cbuffer(double x, int *p, long n, int *q, double y, ...) {
    return nbuffer(x, p, n, q, y);
}
static double consume(int n, ...) {
    va_list ap;
    va_start(ap, n);
    double x = nconsume(ap);
    va_end(ap);
    return x;
}
static float fid(float x) { return x; }
/* Force generic mismatch: one integer word becomes one float word.
   The return is similarly reinterpreted, not numerically converted. */
static unsigned long raw(unsigned long x) { return x >> 32 ? 0 : x; }
static void *ptrid(void *p) { return p; }

int main(int argc, char **argv) {
    void *p = malloc(16);
    int *ip = malloc(sizeof(int));
    *ip = 7;
    switch (atoi(argv[1])) {
    case 0: printf("%.9g\n", nfloat(p, 2.5f)); break;
    case 1: printf("%.17g\n", ndouble(p, 4.0)); break;
    case 2: printf("%.17g\n", ncall(p)); break;
    case 3: printf("%.17g\n", nwide(1, ip, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)); break;
    case 4: printf("%.17g\n", ncallwide(ip)); break;
    case 5: printf("%.17g\n", nindirect(ip)); break;
    case 6: printf("%.17g\n", nvar(4.0, 3, 1.25, 2.5, ip)); break;
    case 7: printf("%.17g\n", ncallvar(ip)); break;
    case 8: printf("%.17g\n", consume(1, 3.25)); break;
    case 9: printf("%.17g\n", nforward(1, 3.25)); break;
    case 10: printf("%d\n", nfloatbits(fid)); break;
    case 11: printf("%d\n", nfloatbits(raw)); break;
    case 12: printf("%d\n", nshort(1, 1.25)); break;
    case 13: printf("%.9g\n", nfloat(NULL, 2.5f)); break;
    case 14: printf("%.17g\n", ndouble((char *)p + 16, 4.0)); break;
    case 15: printf("%lu\n", ((unsigned long (*)(unsigned long))nidentity)(1069547520)); break;
    case 16: printf("%d\n", nforge(ptrid)); break;
    case 17: printf("%.17g\n", nphi(p, 0)); break;
    case 18: printf("%.17g\n", nphi(p, 1)); break;
    case 19: {
        struct pair r = nbuffer(1.25, ip, 10, ip, 2.5);
        printf("%ld %d\n", r.n, *r.p);
        break;
    }
    case 20: printf("%ld\n", ncallbuffer(ip)); break;
    case 21: {
        struct pair r = ((struct pair (*)(unsigned long, int *, long, int *, unsigned long))nbuffer)
            (4608308318706860032UL, ip, 10, ip, 4612811918334230528UL);
        printf("%ld %d\n", r.n, *r.p);
        break;
    }
    case 22: printf("%.17g\n", ndata()); break;
    case 23: printf("%.9g\n", nfloat((char *)p + 12, 2.5f)); break;
    case 24: printf("%.17g\n", ndouble((char *)p + 8, 4.0)); break;
    }
    return 0;
}

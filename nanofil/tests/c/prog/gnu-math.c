#include <stdio.h>
#include <string.h>
#include <errno.h>
static float qn = __builtin_nanf("");
int main(void){
    double xs[] = { -0.5, 0.5, -2.5, 3.0, 1e300, -1e-300, 4503599627370497.0 };
    for (int i = 0; i < 7; i++)
        printf("%g %g\n", __builtin_ceil(xs[i]), __builtin_floor(xs[i]));
    float f = 2.5f;
    printf("%g %g\n", __builtin_ceil(f), __builtin_floor(-f));
    double n = __builtin_nan(""); float nf = __builtin_nanf("");
    unsigned long b; unsigned u, uq; memcpy(&b, &n, 8); memcpy(&u, &nf, 4); memcpy(&uq, &qn, 4);
    printf("%lx %x %x %g\n", b, u, uq, __builtin_ceil(n));
    printf("%g\n", 1.0 / __builtin_ceil(-0.5));
    int sq = 1000001;                   /* cogl_sqrti: an int argument */
    errno = 0;
    double r = __builtin_sqrt(-1.0);
    printf("%d %a %g %d %d\n", (int)__builtin_sqrt(sq), __builtin_sqrt(2.0),
           1.0 / __builtin_sqrt(-0.0), r != r, errno == EDOM);
    return 0;
}

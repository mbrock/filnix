#include <stdio.h>
#include <string.h>
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
    return 0;
}

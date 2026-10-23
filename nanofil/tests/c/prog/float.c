#include <stdio.h>
#include <stdarg.h>
double twice(double x) { return x * 2; }
static double sum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    double result = 0;
    for (int i = 0; i < n; ++i) result += va_arg(ap, double);
    va_end(ap);
    return result;
}
int main(void) {
    float f = 1.25f;
    printf("%g %g %g %g\n", f, twice(f), -0.0, (double)0x1.8p+2f);
    printf("sum %g\n", sum(3, f, 2.5, f + 1));
    return 0;
}

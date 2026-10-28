/* The clang side of shared-thunks.c: definitions, and calls with
   64-bit integers where nanofil's calls pass 32-bit ones. */
#include <stdarg.h>
#include "shared-thunks.h"
long c_isum(int n, ...) {
    va_list ap; va_start(ap, n);
    long s = 0;
    for (int i = 0; i < n; i++) s = s * 3 + va_arg(ap, long);
    va_end(ap);
    return s;
}
double c_mix(int n, ...) {
    va_list ap; va_start(ap, n);
    double d = va_arg(ap, double);
    long *p = va_arg(ap, long *);
    long x = va_arg(ap, long);
    va_end(ap);
    return d + *p * 10 + x * 100 + n;
}
long c_big(BIG_PARAMS) {
    return a + b + c + d + e + f + g + h + i + j + k + l + m + n + o + p
         + q * 1000L + r * 100000L;
}
struct two c_two(long a, long b) { struct two t = { a + b, a - b }; return t; }
long c_calls(void) {
    long big = 0x123456789abLL, q = 2;
    long s = c_isum(11, big, big + 1, big + 2, big + 3, big + 4, big + 5,
                    big + 6, big + 7, big + 8, big + 9, big + 10);
    s ^= (long)c_mix(1, 0.5, &q, big);
    s ^= c_two(big, 1).a;
    s ^= n_isum(9, big, big, big, big, big, big, big, big, big << 4);
    s ^= n_big(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, big, -7, big);
    s ^= n_big_ptr(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, big);
    return s;
}

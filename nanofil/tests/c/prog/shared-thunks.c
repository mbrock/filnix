// link: lib/shared-thunks.c
/* Weak thunks shared by nanofil's and clang's objects (abi-findings.md,
   "Symbols the linker merges"). nanofil's object is linked first, so
   its thunks serve clang's calls too, with 64-bit integers where
   nanofil passes 32-bit ones, on the stack and in registers, mixed with
   doubles, pointers, a two-word result and more than 16 words. shared-thunks-clang.c links
   clang's first. */
#include <stdarg.h>
#include <stdio.h>
#include "lib/shared-thunks.h"
long n_isum(int n, ...) {
    va_list ap; va_start(ap, n);
    long s = 0;
    for (int i = 0; i < n; i++) s = s * 5 + va_arg(ap, long);
    va_end(ap);
    return s;
}
long n_big(BIG_PARAMS) {
    return a - b + c - d + e - f + g - h + i - j + k - l + m - n + o - p
         + q * 7L + r * 3L;
}
long (*n_big_ptr)(BIG_PARAMS) = n_big;
int main(void) {
    int q = 3;
    long lq = q;
    printf("%ld\n", c_isum(11, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11));
    printf("%g\n", c_mix(2, 1.5, &lq, q));
    struct two t = c_two(7, q);
    printf("%ld %ld\n", t.a, t.b);
    printf("%ld\n", c_big(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, -3, 1L << 40));
    long (*cp)(BIG_PARAMS) = c_big;
    printf("%ld\n", cp(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 7));
    printf("%ld\n", c_calls());
    return 0;
}

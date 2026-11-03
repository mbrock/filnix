/* Half checks (docs/half.md): p[-(1 << 47)] lies 2^50 bytes below p, and
   its address wraps past 0, so compared unsigned it is above lower. The
   half check's lower test compares signed and must trap, after printing
   5, with the full check's text, where an unsigned test would let the
   read through to a non-canonical address. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) far(long *p, int k) {
    long a = p[1];
    printf("%ld\n", a);
    fflush(stdout);
    if (k) a += p[-(1L << 47)];
    return a;
}
int main(int argc, char **argv) {
    long *p = calloc(2, sizeof(long));
    p[1] = 5;
    return (int)far(p, argc > 1 ? atoi(argv[1]) : 0);
}

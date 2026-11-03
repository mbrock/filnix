/* Half checks (docs/half.md): under -O --checks=half the checks of p[-1]
   and p[-2] test only the lower bound (signed) and the free flag, since
   the check of p[0] proved the upper one. p points 8 bytes into its
   object, so p[-1] is the object's first word and p[-2] lies below it:
   the read must trap after printing 3 and 4, with the full check's text.
   progtest compares with filcc -O0: at -O1 and -O2 filcc's own lower-only
   check of p[-2] reaches filc_optimized_access_check_fail with a pointer
   whose state it finds valid, and panics ("Should not be reached"). */
// args: 2
// reference-opt: -O0
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) back(long *p, int k) {
    long a = p[0];
    printf("%ld\n", a);
    a += p[-1];
    printf("%ld\n", a);
    fflush(stdout);
    if (k > 1) a += p[-2];
    return a;
}
int main(int argc, char **argv) {
    long *o = calloc(2, sizeof(long));
    o[0] = 1;
    o[1] = 3;
    return (int)back(o + 1, argc > 1 ? atoi(argv[1]) : 0);
}

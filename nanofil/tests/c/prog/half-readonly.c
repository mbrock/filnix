/* Half checks (docs/half.md): t[1]'s write check tests only its upper
   bound and the read-only flag, from the read check of t[0]; t is in
   read-only data, so the write must trap after printing 1, with the
   full check's "read-only" text. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
static const long table[4] = {1, 2, 3, 4};
static long __attribute__((noinline)) poke(long *t, int k) {
    long a = t[0];
    printf("%ld\n", a);
    fflush(stdout);
    if (k) t[1] = a;
    return a;
}
int main(int argc, char **argv) {
    return (int)poke((long *)table, argc > 1 ? atoi(argv[1]) : 0);
}

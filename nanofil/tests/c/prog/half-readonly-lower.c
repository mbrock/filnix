/* Half checks (docs/half.md): t[0]'s write check tests only its lower
   bound and the free and read-only flags, from the read check of t[1];
   t is in read-only data, so the write must trap after printing 2, with
   the full check's "read-only" text. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
static const long table[4] = {1, 2, 3, 4};
static long __attribute__((noinline)) poke(long *t, int k) {
    long a = t[1];
    printf("%ld\n", a);
    fflush(stdout);
    if (k) t[0] = a;
    return a;
}
int main(int argc, char **argv) {
    return (int)poke((long *)table, argc > 1 ? atoi(argv[1]) : 0);
}

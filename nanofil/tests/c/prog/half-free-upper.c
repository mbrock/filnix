/* Half checks (docs/half.md): after the call, s->z's check tests only
   its upper bound, from the check of s->x before it. free sets the
   object's upper to its lower, so the upper test alone must trap, with
   the full check's "free object" text, after printing 1. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
struct S { long x, y, z; };
static void __attribute__((noinline)) maybe_free(struct S *s, int k) {
    if (k) free(s);
}
static long __attribute__((noinline)) get(struct S *s, int k) {
    long a = s->x;
    printf("%ld\n", a);
    fflush(stdout);
    maybe_free(s, k);
    return a + s->z;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, sizeof *s);
    s->x = 1;
    return (int)get(s, argc > 1 ? atoi(argv[1]) : 0);
}

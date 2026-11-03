/* Half checks (docs/half.md): in the loop, s->x's check tests only its
   lower bound and the free flag, from the check of s->y before the
   loop, and s->z's only its upper bound. The call frees s in iteration
   2, so that iteration's first access must trap after printing 0 and 1,
   with the full check's "free object" text. */
// args: 2
#include <stdio.h>
#include <stdlib.h>
struct S { long x, y, z; };
static void __attribute__((noinline)) maybe_free(struct S *s, int i, int k) {
    if (i == k) free(s);
}
static long __attribute__((noinline)) walk(struct S *s, int k) {
    long a = s->y;
    for (int i = 0; i < 10; i++) {
        maybe_free(s, i, k);
        a += s->x;
        s->z = a + i;
        printf("%ld\n", s->z);
        fflush(stdout);
    }
    return a;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, sizeof *s);
    return (int)walk(s, argc > 1 ? atoi(argv[1]) : 100);
}

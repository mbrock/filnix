/* Range guards (docs/m7.md, round 5): under -O --checks=guard the
   loop's read of s->a[i & 3] has no dominating check, so one span test
   before the loop covers [0, 32) of s, and each read tests only the
   free flag. The call frees s in iteration 3, so iteration 4's read must
   trap "free object" after printing 0 to 3, as the full check does.
   tests/renew-trap.sh compares the whole stderr with reference checks. */
// args: 3
#include <stdio.h>
#include <stdlib.h>
struct S { long a[4]; };
static void __attribute__((noinline)) maybe_free(struct S *s, int i, int k) {
    if (i == k) free(s);
}
static long __attribute__((noinline)) sum(struct S *s, int n, int k) {
    long t = 0;
    for (int i = 0; i < n; i++) {
        t += s->a[i & 3];
        maybe_free(s, i, k);
        printf("%d %ld\n", i, t);
        fflush(stdout);
    }
    return t;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, sizeof *s);
    for (int i = 0; i < 4; i++) s->a[i] = i + 1;
    return (int)sum(s, 10, argc > 1 ? atoi(argv[1]) : 100);
}

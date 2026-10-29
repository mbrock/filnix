/* Check renewal (docs/m7.md, round 4) in an irreducible loop: the loop
   {a, b, c} is entered at a or at b, so no block in it dominates the
   others. The read of s->x in a is the only check of s; the store in a
   after a call and the read in c (which only a enters) renew it. The
   call frees s in iteration 3, so the next renew must trap as the full
   check does. tests/renew-trap.sh compares the trap with nanofil's
   reference checks; progtest compares the run with filcc. */
// args: 3 0
#include <stdio.h>
#include <stdlib.h>
struct S { long x, y; };
static void __attribute__((noinline)) maybe_free(struct S *s, int i, int k) {
    if (i == k) free(s);
}
static long __attribute__((noinline)) irr(struct S *s, int k, int start) {
    long t = 0;
    int i = 0;
    if (start) goto b;
a:
    t += s->x;
    maybe_free(s, i, k);
    s->y = t;
    if (i & 1) goto c;
b:
    i++;
    printf("%d %ld\n", i, t);
    fflush(stdout);
    if (i < 8) goto a;
    return t;
c:
    maybe_free(s, i + 100, k);
    t += s->y;
    goto b;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, sizeof *s);
    s->x = 5;
    int k = argc > 1 ? atoi(argv[1]) : 100;
    int start = argc > 2 ? atoi(argv[2]) : 0;
    return (int)irr(s, k, start) & 0x7f;
}

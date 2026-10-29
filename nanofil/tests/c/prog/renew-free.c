/* Check renewal (docs/m7.md, round 4): under -O --checks=renew the
   loop's reads and writes of s->x and s->y after a call renew the check
   made before the loop. The call frees s in iteration 3, so that
   iteration's first access must trap, after printing 0 1 3, as the full
   check does. tests/renew-trap.sh also compares the trap message with
   nanofil's reference checks. */
// args: 3
#include <stdio.h>
#include <stdlib.h>
struct S { long x, y; struct S *next; };
static void __attribute__((noinline)) maybe_free(struct S *s, int i, int k) {
    if (i == k) free(s);
}
static long __attribute__((noinline)) walk(struct S *s, int k) {
    long a = s->x + s->y;
    for (int i = 0; i < 10; i++) {
        maybe_free(s, i, k);
        s->x += i;
        s->y = s->x;
        s->next = malloc(sizeof *s);
        printf("%ld\n", s->x);
        fflush(stdout);
    }
    return a + s->y;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, sizeof *s);
    return (int)walk(s, argc > 1 ? atoi(argv[1]) : 100);
}

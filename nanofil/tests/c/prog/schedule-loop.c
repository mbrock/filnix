// Scheduled checks (docs/schedule.md) do not cross an edge back: the
// loop reads s->v[i] for i below n, and only the last iteration's read
// is out of bounds, so the loop's earlier iterations run and print, in
// every build, before the trap.
#include <stdio.h>
#include <stdlib.h>
struct S { int n; int v[4]; };
static long __attribute__((noinline)) f(struct S *s, int n) {
    long t = 0;
    for (int i = 0; i < n; i++) {
        t += s->v[i];
        printf("%d\n", i);
        fflush(stdout);
    }
    return t;
}
int main(void) {
    struct S *s = calloc(1, sizeof *s);
    printf("%ld\n", f(s, 12));
    return 0;
}

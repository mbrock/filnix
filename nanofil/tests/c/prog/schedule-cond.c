// Scheduled checks (docs/schedule.md) check early only bytes that every
// path ahead accesses: s->z is read on one arm only, so the check of
// s->a must not cover it, and the call with flag 0 on a short object
// does not trap. The call with flag 1 traps at s->z in every build.
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
struct S { int a; int pad[31]; int z; };
static long __attribute__((noinline)) f(struct S *s, int flag) {
    long t = s->a;
    if (flag)
        t += s->z;
    return t;
}
int main(void) {
    struct S *s = calloc(1, offsetof(struct S, z));
    printf("%ld\n", f(s, 0));
    fflush(stdout);
    printf("%ld\n", f(s, 1));
    return 0;
}

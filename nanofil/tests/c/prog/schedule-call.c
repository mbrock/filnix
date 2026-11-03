// Scheduled checks (docs/schedule.md) do not move a check over a call:
// f prints between reading s->a and s->z, so every build prints
// "between" before trapping at s->z, as filcc -O2 does (printf may not
// return, so its scheduler stops there too).
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
struct S { int a; int pad[31]; int z; };
static long __attribute__((noinline)) f(struct S *s) {
    long t = s->a;
    printf("between\n");
    fflush(stdout);
    t += s->z;
    return t;
}
int main(void) {
    struct S *s = calloc(1, offsetof(struct S, z));
    printf("%ld\n", f(s));
    return 0;
}

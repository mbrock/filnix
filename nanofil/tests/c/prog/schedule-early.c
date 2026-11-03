// early
// Scheduled checks (docs/schedule.md): f reads s->a, stores through p,
// then reads s->z, past the end of a short object. With
// --checks=schedule the check of s->a is widened over s->z and traps
// before the store, naming the merged size, as filcc -O2 does; the
// reference checks trap at s->z. schedule-trap.sh compares the three.
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
struct S { int a; int pad[31]; int z; };
static long __attribute__((noinline)) f(struct S *s, int *p) {
    long t = s->a;
    *p = 7;
    t += s->z;
    return t;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, argc > 1 ? sizeof *s : offsetof(struct S, z));
    printf("start\n");
    fflush(stdout);
    int *g = malloc(sizeof *g);
    long r = f(s, g);
    printf("%ld %d\n", r, *g);
    return 0;
}

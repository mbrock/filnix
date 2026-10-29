/* Check renewal (docs/m7.md, round 4): under -O --checks=renew the
   loop's reads of *n after a call renew the read check made before the
   loop. t holds a pointer, so it stays in .data with the read-only aux
   flag: a read renewal must test only the free flag, or these reads of
   const data would trap. (tests/renew-trap.sh runs only the trapping
   renew-*.c.) */
#include <stdio.h>
static int v = 7;
static const struct { int *p; int n; } t = { &v, 1 };
static void __attribute__((noinline)) tick(int i) { printf("%d\n", i); fflush(stdout); }
static int __attribute__((noinline)) sum(const int *n) {
    int s = *n;
    for (int i = 0; i < 3; i++) {
        tick(i);
        s += *n + i;
    }
    return s;
}
int main(void) {
    printf("%d %d\n", sum(&t.n), *t.p);
    return 0;
}

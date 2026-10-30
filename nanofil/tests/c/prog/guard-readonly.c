/* Range guards (docs/m7.md, round 5): the writes to n[i & 1] in the
   loop, which no read of the same span precedes, are guarded by one span
   test of n, and the guard passes, so each write tests the read-only
   flag itself. t holds a pointer, so it stays
   in .data with the read-only aux flag: the write in iteration 2 must
   trap as the full write check does, after 0 and 1 print. */
#include <stdio.h>
static int v = 7;
static const struct { int *p; int n[2]; } t = { &v, { 1, 2 } };
static int __attribute__((noinline)) tick(int i) { printf("%d\n", i); fflush(stdout); return i; }
static int __attribute__((noinline)) bump(int *n, int k) {
    int s = 0;
    for (int i = 0; i < 5; i++) {
        s += i;
        if (tick(i) == k) n[i & 1] = s;
    }
    return s;
}
int main(void) {
    int z[2] = { 3, 4 };
    printf("%d %d\n", bump(z, 1), *t.p);
    fflush(stdout);
    return bump((int *)t.n, 2);
}

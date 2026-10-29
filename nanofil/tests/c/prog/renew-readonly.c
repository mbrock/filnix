/* Check renewal (docs/m7.md, round 4): a write after a call renews a
   read's check of the same pointer, testing the read-only flag as well
   as the free one. t holds a pointer, so it stays in .data with the
   read-only aux flag: the write in the loop's third iteration must trap
   as the full write check does, after the first two print. */
#include <stdio.h>
static int v = 7;
static const struct { int *p; int n; } t = { &v, 1 };
static int __attribute__((noinline)) tick(int i) { printf("%d\n", i); fflush(stdout); return i; }
static int __attribute__((noinline)) bump(int *n, int k) {
    int s = *n;
    for (int i = 0; i < 5; i++)
        if (tick(i) == k) *n = s + i;
    return s;
}
int main(void) {
    int z = 0;
    bump(&z, 1);
    printf("%d %d\n", z, *t.p);
    fflush(stdout);
    return bump((int *)&t.n, 2);
}

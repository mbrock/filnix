/* Hoisted bounds (docs/bounds.md): the writes to n[k[i]] are tested
   against a limit of n taken before the loop and the read-only flag
   at each write. t holds a pointer, so it stays in .data with the
   read-only aux flag: the write in iteration 2 must trap as the full
   write check does, after 0 and 1 print. */
#include <stdio.h>
static int v = 7;
static const struct { int *p; int n[2]; } t = { &v, { 1, 2 } };
static const int k[5] = { 0, 1, 1, 0, 1 };
static int __attribute__((noinline)) tick(int i) { printf("%d\n", i); fflush(stdout); return i; }
static int __attribute__((noinline)) bump(int *n, int w) {
    int s = 0;
    for (int i = 0; i < 5; i++) {
        s += i;
        if (tick(i) == w) n[k[i]] = s;
    }
    return s;
}
int main(void) {
    int z[2] = { 3, 4 };
    printf("%d %d\n", bump(z, 1), *t.p);
    fflush(stdout);
    return bump((int *)t.n, 2);
}

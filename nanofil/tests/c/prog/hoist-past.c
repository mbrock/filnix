/* Hoisted bounds (docs/bounds.md): a[idx[i]] is tested against a limit
   of a taken before the loop. idx walks to one element past the end of
   the 16-byte object in iteration 5, which must trap out of bounds
   after printing 0 to 4, as the full check does. tests/renew-trap.sh compares the whole stderr with reference
   checks. */
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) sum(int *a, const int *idx, int n) {
    long t = 0;
    for (int i = 0; i < n; i++) {
        t += a[idx[i]];
        printf("%d %ld\n", i, t);
        fflush(stdout);
    }
    return t;
}
int main(void) {
    int *a = calloc(4, sizeof *a);
    int idx[8] = { 0, 3, 2, 1, 3, 4, 0, 0 };
    for (int i = 0; i < 4; i++) a[i] = i + 1;
    return (int)sum(a, idx, 8);
}

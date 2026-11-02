/* Hoisted bounds (docs/bounds.md): under -O --checks=hoist the loop's
   read of a[idx[i]] tests its bounds against a limit of a taken before
   the loop, since its offset is loaded in the loop and no guard covers
   it. The call frees a in iteration 3; the limit still holds a's old
   upper, so iteration 4's read must trap "free object" on the free flag,
   after printing 0 to 3, as the full check does. tests/renew-trap.sh
   compares the whole stderr with reference checks. */
// args: 3
#include <stdio.h>
#include <stdlib.h>
static void __attribute__((noinline)) maybe_free(long *a, int i, int k) {
    if (i == k) free(a);
}
static long __attribute__((noinline)) sum(long *a, const int *idx, int n, int k) {
    long t = 0;
    for (int i = 0; i < n; i++) {
        t += a[idx[i]];
        maybe_free(a, i, k);
        printf("%d %ld\n", i, t);
        fflush(stdout);
    }
    return t;
}
int main(int argc, char **argv) {
    long *a = calloc(8, sizeof *a);
    int idx[10];
    for (int i = 0; i < 8; i++) a[i] = i + 1;
    for (int i = 0; i < 10; i++) idx[i] = (i * 5) % 8;
    return (int)sum(a, idx, 10, argc > 1 ? atoi(argv[1]) : 100);
}

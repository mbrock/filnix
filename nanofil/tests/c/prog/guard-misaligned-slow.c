/* Range guards (docs/m7.md, round 5): as guard-misaligned.c, but buf
   has only two slots, so the span test of pp = buf + 1 byte fails and
   each load runs its full check out of line, which must trap on the
   alignment as the reference does. */
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) count(void **pp, int n) {
    long c = 0;
    for (int i = 0; i < n; i++)
        c += pp[i & 1] != 0;
    return c;
}
int main(void) {
    void **buf = calloc(2, sizeof(void *));
    buf[0] = buf;
    printf("%ld\n", count(buf, 3));
    fflush(stdout);
    return (int)count((void **)((char *)buf + 1), 3);
}

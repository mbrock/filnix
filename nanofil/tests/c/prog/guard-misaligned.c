/* Range guards (docs/m7.md, round 5): the guarded pointer loads of
   pp[i & 1] test alignment themselves when the guard passed. pp is one
   byte past an 8-aligned buffer, so the first load must trap as the full
   check does, after the line before the loop. */
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) count(void **pp, int n) {
    long c = 0;
    for (int i = 0; i < n; i++)
        c += pp[i & 1] != 0;
    return c;
}
int main(void) {
    void **buf = calloc(4, sizeof(void *));
    buf[0] = buf;
    printf("%ld\n", count(buf, 3));
    fflush(stdout);
    return (int)count((void **)((char *)buf + 1), 3);
}

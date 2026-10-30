/* Range guards (docs/m7.md, round 5): as guard-short.c, the span test
   of t fails and every read runs its full check, but the loop keeps
   more scalars live than temps mode homes alone, so frame slots are
   shared by liveness (docs/perf.md 3d). The guard's slot must stay live
   through the loop: were another value to reuse it, a nonzero G would
   skip the bounds test. The read of t[240] must trap after three lines. */
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) mix(const unsigned char *t, const unsigned char *in, int n) {
    long a0 = 1, a1 = 2, a2 = 3, a3 = 4, a4 = 5, a5 = 6, a6 = 7, a7 = 8, a8 = 9, a9 = 10;
    long b0 = 11, b1 = 12, b2 = 13, b3 = 14, b4 = 15, b5 = 16, b6 = 17, b7 = 18, b8 = 19, b9 = 20;
    for (int i = 0; i < n; i++) {
        long v = t[in[i]];
        a0 += v; a1 ^= a0; a2 += a1 * 3; a3 -= a2; a4 += a3 >> 1; a5 ^= a4; a6 += a5; a7 -= a6;
        a8 += a7 * 5; a9 ^= a8; b0 += a9; b1 -= b0; b2 ^= b1; b3 += b2 * 7; b4 -= b3; b5 ^= b4;
        b6 += b5; b7 -= b6; b8 ^= b7; b9 += b8;
        printf("%d %ld\n", i, a0 + a5 + b9);
        fflush(stdout);
    }
    return a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9;
}
int main(void) {
    unsigned char *t = malloc(240);
    for (int i = 0; i < 240; i++) t[i] = (unsigned char)i;
    static const unsigned char in[] = { 1, 239, 7, 240, 3 };
    return (int)mix(t, in, 5);
}

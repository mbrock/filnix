/* Range guards (docs/m7.md, round 5): t[c] for a byte c spans 256
   bytes, but t has 240 (a multiple of 16, so no rounding hides the
   end), so the span test before the loop fails and every read runs its
   full check. The read of t[240], the fourth, must trap out of bounds
   after three lines, as the full check does. */
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) lookup(const unsigned char *t, const unsigned char *in, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) {
        s += t[in[i]];
        printf("%d %ld\n", i, s);
        fflush(stdout);
    }
    return s;
}
int main(void) {
    unsigned char *t = malloc(240);
    for (int i = 0; i < 240; i++) t[i] = (unsigned char)i;
    static const unsigned char in[] = { 1, 239, 7, 240, 3 };
    return (int)lookup(t, in, 5);
}

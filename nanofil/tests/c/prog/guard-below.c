/* Range guards (docs/m7.md, round 5): mid[c] for a signed byte c spans
   [-512, 508) of mid, but mid is only 64 bytes into its object, so the
   span test must fail on the lower end and every read runs its full
   check. The read of mid[-100], the third, must trap below lower after
   two lines, as the full check does. */
#include <stdio.h>
#include <stdlib.h>
static long __attribute__((noinline)) sum(const int *mid, const signed char *in, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) {
        s += mid[in[i]];
        printf("%d %ld\n", i, s);
        fflush(stdout);
    }
    return s;
}
int main(void) {
    int *w = calloc(256, sizeof(int));
    for (int i = 0; i < 256; i++) w[i] = i;
    static const signed char in[] = { 3, -16, -100, 5 };
    return (int)sum(w + 16, in, 4);
}

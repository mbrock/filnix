// Forward facts (docs/forward.md): g reads p[0], p[2^32] and p[5]; the
// hull of the first two covers p[5], and the reader must be p[0]'s
// proof, the nearest, since a reused access's offset is 32 bits (a
// review's counterexample: the farthest reader failed to compile).
#include <stdio.h>
#include <stdlib.h>
long __attribute__((noinline)) f(char *p) {
    long t = p[0x100000000L];
    t += p[0];
    t += p[5];
    return t;
}
long __attribute__((noinline)) g(char *p) {
    long t = p[0];
    t += p[0x100000000L];
    t += p[5];
    return t;
}
int main(void) {
    char *p = calloc(1, 0x100000010L);
    if (!p) return 1;
    p[5] = 7;
    printf("%ld %ld\n", f(p), g(p));
    return 0;
}

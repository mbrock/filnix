/* malloc, calloc, realloc, free and the aligned allocators, driven by a
   fixed pseudo-random sequence; every block holds a pattern that is
   checked before it is resized or freed, and the result is a checksum. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint32_t seed = 12345;
static uint32_t next(void) { seed = seed * 1103515245u + 12345u; return seed >> 8; }

int main(void)
{
    enum { N = 512 };
    unsigned char *p[N] = { 0 };
    size_t sz[N] = { 0 };
    unsigned long sum = 0, bad = 0;
    for (int round = 0; round < 20000; round++) {
        int i = next() % N;
        if (p[i]) {
            for (size_t k = 0; k < sz[i]; k++) bad += p[i][k] != (unsigned char) (i + k);
            if (next() % 3 == 0) {
                size_t ns = next() % 4096;
                unsigned char *q = realloc(p[i], ns ? ns : 1);
                if (!q) return 3;
                for (size_t k = 0; k < (ns < sz[i] ? ns : sz[i]); k++) bad += q[k] != (unsigned char) (i + k);
                p[i] = q; sz[i] = ns;
                for (size_t k = 0; k < ns; k++) q[k] = (unsigned char) (i + k);
                continue;
            }
            free(p[i]); p[i] = NULL;
        } else {
            sz[i] = next() % (next() % 8 ? 256 : 65536);
            p[i] = next() % 4 ? malloc(sz[i] ? sz[i] : 1) : calloc(sz[i] ? sz[i] : 1, 1);
            if (!p[i]) return 3;
            for (size_t k = 0; k < sz[i]; k++) p[i][k] = (unsigned char) (i + k);
            sum += sz[i];
        }
    }
    void *a = aligned_alloc(64, 640), *b = NULL;
    int pm = posix_memalign(&b, 256, 1000);
    printf("aligned %d %d %d\n", (int) ((uintptr_t) a % 64), pm, (int) ((uintptr_t) b % 256));
    free(a); free(b);
    for (int i = 0; i < N; i++) free(p[i]);
    printf("allocated %lu bad %lu\n", sum, bad);
    return bad != 0;
}

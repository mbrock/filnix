// Runtime axiom "Non-moving" (docs/runtime-axioms.md): an object's
// address is stable for its lifetime, across many collections. The
// collector does move one thing: a stored pointer to a freed object gets
// the free singleton's capability. Its address stays, so the obvious
// wrong strengthening, that the collector leaves a stored pointer
// exactly as it was, is refuted by the aux probe (axiom-aux.c); this one
// requires that addresses, live or freed, never change.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
enum { N = 256 };
static long *objs[N];
static uintptr_t addrs[N];
int main(void) {
    for (int i = 0; i < N; i++) {
        objs[i] = malloc(32);
        addrs[i] = (uintptr_t)objs[i];
        for (int j = 0; j < 4; j++) objs[i][j] = i * 4 + j;
    }
    for (int i = 0; i < N; i += 2) free(objs[i]);
    for (int round = 0; round < 6; round++) {
        for (int k = 0; k < 4000; k++) { long *g = malloc(32); g[0] = k; }
        zgc_request_and_wait();
    }
    int stable = 1, intact = 1;
    for (int i = 0; i < N; i++) {
        if ((uintptr_t)objs[i] != addrs[i]) stable = 0;
        if (i % 2)
            for (int j = 0; j < 4; j++) if (objs[i][j] != i * 4 + j) intact = 0;
    }
    printf("addresses unchanged, live and freed: %s\n", stable ? "yes" : "no");
    printf("live objects intact: %s\n", intact ? "yes" : "no");
    return 0;
}

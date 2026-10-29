// reference-opt: -O0
/* A pointer rebuilt from integer arithmetic has no capability, the
   Fil-C rule (docs/ub.md, *A pointer rebuilt from integers*): libgcrypt's
   sexp_null_cond masks (uintptr_t)w with masks from volatiles and casts
   the result back. filcc -O0 traps on *q, as nanofil does; filcc -O1
   and -O2 print 42, because LLVM folds the round trip into a pointer
   operation before pizlonation. The reference is therefore -O0. */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

volatile unsigned int vzero = 0, vone = 1;

static inline uintptr_t gen_mask(unsigned long op) { return (uintptr_t)vzero - (uintptr_t)op; }
static inline uintptr_t gen_inv_mask(unsigned long op) { return (uintptr_t)op - (uintptr_t)vone; }
static inline uintptr_t sel(uintptr_t a, uintptr_t b, unsigned long op) {
    uintptr_t mb = gen_inv_mask(op), ma = gen_mask(op);
    return (ma & a) | (mb & b);
}
static inline int *null_cond(int *w, unsigned long op) {
    uintptr_t o = sel((uintptr_t)NULL, (uintptr_t)w, op);
    return (int *)(void *)o;
}

int main(void) {
    int *p = malloc(sizeof *p);
    *p = 42;
    int *q = null_cond(p, 0);
    int *z = null_cond(p, 1);
    printf("%d %d\n", q == p, z == NULL);
    fflush(stdout);
    printf("%d\n", *q);             /* traps: q has no capability */
    return 0;
}

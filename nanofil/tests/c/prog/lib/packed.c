/* The clang side of packed.c. */
#include "packed.h"
struct pk c_pk(long x) { struct pk p = { 1, x * 3, (short)-x }; return p; }
long c_pk_sum(struct pk *p) { struct pk q = n_pk(p->b); return q.a + q.b + q.c; }

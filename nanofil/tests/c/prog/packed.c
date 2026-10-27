// link: lib/packed.c
/* A misaligned packed struct returned by value across the nanofil/clang
   boundary in both directions (lib/packed.c is built by clang). */
#include <stdio.h>
#include "lib/packed.h"
struct pk n_pk(long x) { struct pk p = { 2, x + 5, 7 }; return p; }
int main(void) {
    struct pk p = c_pk(4);
    printf("%d %lld %d\n", p.a, p.b, p.c);
    printf("%ld\n", c_pk_sum(&p));
    return 0;
}

// nanofil-link: lib/static-prior.c
/* A function declared static, then defined without a storage class or
   with extern, has internal linkage (C11 6.2.2p4-5), as libevent's
   min_heap_ctor_ is declared static inline in a header and defined
   without static. Two units do so here, so exported symbols would
   collide at link. */
#include <stdio.h>

static inline int heap_size(const int *s);
int heap_size(const int *s) { return s[0]; }
static int helper(void);
int helper(void) { return 1; }
static void later(void);
void later(void);
void later(void) { puts("later"); }

int other_unit(void);

int main(void)
{
    int s[1] = {7};
    later();
    printf("%d %d %d\n", heap_size(s), helper(), other_unit());
    return 0;
}

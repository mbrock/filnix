/* The difference of two addresses built from integer constants is an
   integer constant (clang folds it; C11 6.6p10 allows the form):
   ghostscript's offset_of, (char *)&((T *)0)->m - (char *)((T *)0), in
   static initializers and case labels, counted in elements. */
#include <stdio.h>
struct d { void *next; long x; int y[3]; };
#define offset_of(type, memb) ((int) ( (char *)&((type *)0)->memb - (char *)((type *)0) ))
static const struct { unsigned short t, o; } elts[] = { { 0, offset_of(struct d, next) }, { 0, offset_of(struct d, y[2]) } };
static const long z = (long *)&((struct d *)0)->y - (long *)0;
int main(void) {
    int k = 2;
    switch (k) { case offset_of(struct d, x) / 4: puts("case"); }
    printf("%d %d %zu %ld\n", elts[0].o, elts[1].o, sizeof elts / sizeof elts[0], z);
    return 0;
}

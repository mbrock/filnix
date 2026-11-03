/* Shared check parts (docs/perf.md item 17): under -O --share=upper the
   check of p->b skips its null test, since the check of p->a in its
   block tested p's lower, but must load p's upper again: free(p) between
   the two accesses set upper = lower. The read of p->b must trap "free
   object" as filcc -O2's does. Its functions are external, since nanofil -O inlines small static
   functions whatever their attributes. tests/share-trap.sh compares. */
#include <stdio.h>
#include <stdlib.h>
struct S { int a; int b; long c; };
int __attribute__((noinline)) fields(struct S *p) {
    int x = p->a;
    free(p);
    return x + p->b;
}
int main(void) {
    struct S *p = malloc(sizeof *p);
    p->a = 1; p->b = 2; p->c = 3;
    printf("%d\n", fields(p));
    return 0;
}

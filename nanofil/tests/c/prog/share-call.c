/* Shared check parts (docs/perf.md item 17): a call between two checks
   of one object ends the reuse of its upper, whatever the callee does.
   Here the callee frees the object, so the read of p->b after it must
   trap "free object" as filcc -O2's does, though the check of p->a just
   before the call loaded p's upper. Its functions are external, since nanofil -O inlines small static
   functions whatever their attributes. tests/share-trap.sh compares. */
#include <stdio.h>
#include <stdlib.h>
struct S { int a; int b; long c; };
void __attribute__((noinline)) release(struct S *p) { free(p); }
int __attribute__((noinline)) fields(struct S *p) {
    int x = p->a;
    release(p);
    return x + p->b;
}
int main(void) {
    struct S *p = malloc(sizeof *p);
    p->a = 1; p->b = 2; p->c = 3;
    printf("%d\n", fields(p));
    return 0;
}

/* Shared check parts (docs/perf.md item 17): the check of p->a does not
   dominate the check of p->b, so under -O --share=null the latter keeps
   its null test, and with p null and c = 0 it must trap as filcc -O2's
   does. The second check of p->a, after p->b's, shares both parts. Taking facts from a predecessor that is not a dominator would
   read upper below address 0 instead. Its functions are external, since nanofil -O inlines small static
   functions whatever their attributes. tests/share-trap.sh compares. */
// args: 0
#include <stdio.h>
#include <stdlib.h>
struct S { int a; int b; };
int __attribute__((noinline)) f(struct S *p, int c) {
    int x = 0;
    if (c) x = p->a;
    x += p->b;
    return x + p->a;
}
int main(int argc, char **argv) {
    struct S s = { 1, 2 };
    printf("%d\n", f(&s, 1));
    fflush(stdout);
    printf("%d\n", f(atoi(argv[1]) ? &s : NULL, atoi(argv[1])));
    return 0;
}

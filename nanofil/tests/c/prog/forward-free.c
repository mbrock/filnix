// Forward facts (docs/forward.md): f reads s->a and the pointer s->p,
// then s->b, which the hull of those two checks covers, and s->p again,
// a pointer load reading the earlier proof. After free(s) nothing is
// reused: the next read of s->a keeps its check and traps there, with
// the reference build's text (renew-trap.sh), as filcc's does.
// args: 1
#include <stdio.h>
#include <stdlib.h>
struct S { int a; int pad; int b; char *p; };
static long __attribute__((noinline)) f(struct S *s, int k) {
    long t = s->a;
    char *p = s->p;
    t += s->b;
    char *p2 = s->p;
    t += p[0] + p2[1];
    printf("%ld\n", t);
    fflush(stdout);
    if (k)
        free(s);
    t += s->a;
    return t;
}
int main(int argc, char **argv) {
    struct S *s = malloc(sizeof *s);
    s->a = 1; s->b = 2; s->p = "AB";
    printf("%ld\n", f(s, argc > 1));
    return 0;
}

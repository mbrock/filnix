/* Half checks (docs/half.md): under -O --checks=half the check of s->z
   tests only its upper bound, since the check of s->x before it proved
   the capability and the lower one. The object is 16 bytes, too short
   for s->z, so the read must trap after printing 7, with the full
   check's text. tests/renew-trap.sh compares it with reference checks. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
struct S { long x, y, z, w; };
static long __attribute__((noinline)) get(struct S *s, int k) {
    long a = s->x;
    printf("%ld\n", a);
    fflush(stdout);
    if (k) a += s->z;
    return a;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, 16);
    s->x = 7;
    return (int)get(s, argc > 1 ? atoi(argv[1]) : 0);
}

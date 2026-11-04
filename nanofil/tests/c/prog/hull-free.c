/* Renewal by the hull of two checks (docs/forward.md): after the call,
   s->b's check becomes a flag test reading the checks of s->a and s->c,
   which no single check covers. The call frees s when asked, so the
   read of s->b must trap with the full check's "free object" text. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
struct S { long a, b, c; };
static void __attribute__((noinline)) maybe_free(struct S *s, int k) {
    if (k) free(s);
}
static long __attribute__((noinline)) walk(struct S *s, int k) {
    long t = s->a + s->c;
    maybe_free(s, k);
    t += s->b;
    return t;
}
int main(int argc, char **argv) {
    struct S *s = calloc(1, sizeof *s);
    s->a = 1; s->b = 2; s->c = 3;
    printf("%ld\n", walk(s, 0));
    fflush(stdout);
    printf("%ld\n", walk(s, argc > 1 ? atoi(argv[1]) : 0));
    return 0;
}

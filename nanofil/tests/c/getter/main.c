/* Getters (docs/forward.md): every copy of an external getter may run
   user code. The first copy of f's getter runs its ifunc resolver
   (lib.c), which frees s: g's read of s->b after it must trap with the
   full check's "free object" text, though s->a's check came before. f0's
   resolver returns null, so its getter runs it again at the second copy,
   which frees s: k's second read of s->b must trap too, though the copy
   is dominated by another. In h the second copy of the static function
   local's getter is a repeated getter of a local symbol, whose fast path
   frees nothing, so the checks of s before it still hold after it. */

#include <stdio.h>
#include <stdlib.h>
struct S { long a, b, c; };
extern struct S *victim, *victim2;
void f(void);
void f0(void);
static volatile long sink;
static void __attribute__((noinline)) local(void) { }
__attribute__((noinline)) long h(struct S *s) {
    long t = s->a + s->c;
    sink = (long)local;
    t += s->b;
    sink = (long)local;
    t += s->a + s->b + s->c;
    return t;
}
__attribute__((noinline)) long g(struct S *s) {
    long t = s->a + s->c;
    sink = (long)f;
    t += s->b;
    return t;
}
__attribute__((noinline)) long k(struct S *s) {
    long t = s->a + s->c;
    sink = (long)f0;
    t += s->b;
    sink = (long)f0;
    t += s->b;
    return t;
}
int main(int argc, char **argv) {
    victim = calloc(1, sizeof *victim);
    victim->a = 1; victim->b = 2; victim->c = 3;
    victim2 = calloc(1, sizeof *victim2);
    struct S *other = calloc(1, sizeof *other);
    int mode = argc > 1 ? atoi(argv[1]) : 0;
    printf("%ld\n", h(other));
    fflush(stdout);
    printf("%ld\n", mode == 1 ? g(victim) : mode == 2 ? k(victim2) : h(other));
    return 0;
}

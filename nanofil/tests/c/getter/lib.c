/* Built by filcc for tests/getter-trap.sh: an ifunc whose resolver, run
   by the first call of f's getter, frees `victim` and stores a pointer,
   and an ifunc f0 whose resolver returns null, so its getter publishes
   no cache and runs it at every call: the second call frees `victim2`
   (docs/forward.md, Getters). nanofil does not compile ifuncs. */
#include <stdio.h>
#include <stdlib.h>
struct S { long a, b, c; };
struct S *victim;
void *kept;
static void impl(void) { }
static void (*resolve(void))(void) {
    kept = malloc(32);
    free(victim);
    return impl;
}
void f(void) __attribute__((ifunc("resolve")));
struct S *victim2;
static int calls;
static void (*resolve0(void))(void) {
    if (++calls == 2) free(victim2);
    return 0;
}
void f0(void) __attribute__((ifunc("resolve0")));

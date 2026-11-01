/* Idioms of upstream Fil-C's tests (docs/filc-tests.md) that nanofil
   once got wrong. An asm label on a declaration names the definition
   that follows (asmname): lib/filc-suite-idioms.c calls `renamed`.
   Equal string literals are one object, as clang merges them (struct,
   weakmap). Destructors without a priority run in reverse declaration
   order (exittest). filc_test_support.h's memmoves are the runtime's
   zmemmove and zhas_union does nothing (zmemmove_union*). A GNU
   attribute may begin a statement (musttail). */
// link: lib/filc-suite-idioms.c
#include <filc_test_support.h>
#include <stdio.h>
#include <string.h>

void named(void) __asm__("renamed");
void named(void) { puts("renamed definition"); }
void call_renamed(void);

static const char *greeting(void) { return "hello"; }

/* Declared in the opposite of their names' order, which nanofil once
   emitted them in. */
__attribute__((destructor)) static void zulu(void) { puts("destructor zulu, declared first"); }
__attribute__((destructor)) static void alpha(void) { puts("destructor alpha, declared second"); }

static long count(long n, long acc)
{
    if (n == 0)
        return acc;
    __attribute__((musttail)) return count(n - 1, acc + 1);
}

int main(void)
{
    call_renamed();
    printf("same literal: %d\n", greeting() == "hello");
    struct { char *p; long n; } a = { "x", 7 }, b;
    zhas_union(&b);
    zmemmove_union(&b, &a, sizeof a);
    zmemmove_builtin(&b.n, &a.n, sizeof a.n);
    printf("%s %ld\n", b.p, b.n);
    printf("count %ld\n", count(1000, 0));
    return 0;
}

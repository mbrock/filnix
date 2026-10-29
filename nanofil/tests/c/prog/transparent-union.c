// link: lib/transparent-union.c
// signatures
/* GNU transparent_union parameters across the nanofil/clang boundary:
   a union of one eightbyte passes as its first member, so each function
   here has the Fil-C signature clang gives it. An argument initializes
   the member of its own type, never the first by reinterpretation: a
   long given for WordArg leaves p without a capability, and the last
   line dereferences it, which traps in both builds. */
#include <stdio.h>
#include "lib/transparent-union.h"

long n_ptr(PtrArg a) { return a.ip ? *a.ip : -1; }
long n_word(WordArg w) { return (long)w.p % 1000; }
int n_int(union IntArg a) { return (int)a.u * 2; }
long n_mixed(Mixed m) { return m.l + 1; }

static long take_ints(int *p) { return *p + 1000; }
static void *copy(void *p) { return p; }

static long register_copy(const char *name, void *(*f)(void *)) { return name[0] + (f != 0); }

static int deref_word(WordArg w) { return *(char *)w.p; }

int main(void)
{
    int x = 7;
    long y = 8;
    const char *s = "s";
    /* GLib's _g_register_boxed: a pointer to a function taking member
       types initializes a pointer with transparent union parameters. */
    long (*reg)(const char *,
                union { void *(*f)(void *); long (*g)(int *); } __attribute__((__transparent_union__))) =
        register_copy;
    long (*tp)(PtrArg) = take_ints;
    Mixed m;
    m.i = 3;
    m.l = 21;
    printf("c: %ld %ld %ld %ld %ld\n", c_ptr(&x), c_ptr(&y), c_ptr(s), c_ptr(NULL), c_ptr(0));
    printf("c: %ld %ld %d %d %ld\n", c_word(&x) != 0, c_word(14L), c_int(4), c_int(4u), c_mixed(m));
    printf("n: %ld %ld %ld %ld %d %ld\n", n_ptr(&x), n_word(5L), n_word((void *)0), n_word(1234L),
           n_int(-2), n_mixed(m));
    printf("fp: %ld %ld %ld %ld\n", tp(&x), reg("A", copy), reg("B", take_ints), c_calls());
    fflush(stdout);
    return deref_word(12345L);
}

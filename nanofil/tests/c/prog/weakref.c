// link: lib/weakref.c
/* GNU's weakref (c_lower weakref_item/3): a static declaration that
   refers to another symbol. Ruby's anyargs.h declares weakrefs of one
   function with different parameter types, to type-check its dispatch.
   A target nothing defines reads as null. noescape is a hint. */
#include <stdio.h>
int target(int x);
static int ref1(int x) __attribute__((weakref("target")));
static int ref2(long x) __attribute__((__weakref__("target")));
static int missing_ref(int) __attribute__((weakref("not_defined_anywhere")));
__attribute__((weakref("other"))) static int ref3(int);
static int ref4(int) __attribute__((weakref, alias("other")));
static int apply_int(int (*)(int), int) __attribute__((weakref("apply")));
static int apply_long(int (*)(long), int) __attribute__((weakref("apply")));
static int twice(int x) { return 2 * x; }
static int twice_l(long x) { return (int)(3 * x); }
static void fill(int *p __attribute__((noescape))) { *p = 7; }
int main(void) {
    int v = 0; fill(&v);
    printf("%d %d %d %d %d\n", ref1(1), ref2(2), missing_ref ? 1 : 0, ref3(5), ref4(6));
    printf("%d %d %d %d\n", apply_int(twice, 4), apply_long(twice_l, 4), target == ref1, v);
    return 0;
}

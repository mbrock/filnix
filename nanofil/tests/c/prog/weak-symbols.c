// link: lib/weak-symbols.c
/* Weak symbols (__attribute__((weak)), #pragma weak, weak aliases)
   between a nanofil and a clang object (abi-findings.md, *Weak
   symbols*): weak definitions used alone and overridden by a strong one
   in the other object, in both directions; a name weak in both, which
   both objects must see as one definition; unresolved weak functions
   and data tested for null, called only when present, and their
   addresses taken in code and in a static initializer.
   weak-symbols-clang.c links clang's object first. */
#include <stdio.h>
#include "lib/weak-symbols.h"
__attribute__((weak)) int n_weak_alone(int x) { return x * 7; }
__attribute__((weak)) int n_weak_overridden(int x) { return -x; }
int c_weak_overridden(int x) { return x + 2000; }
__attribute__((weak)) int n_wdata_overridden = 5;
int c_wdata_overridden = 9;
__attribute__((weak)) int both_weak(void) { return 1; }
#pragma weak n_pragma
int n_pragma(void) { return 40; }
static int n_real(int x) { return x * 11; }
int n_alias(int x) __attribute__((weak, alias("n_real")));
int n_strong_for_c(int x) { return x * 100; }
extern int n_missing(int) __attribute__((weak));
extern int n_missing_data __attribute__((weak));
#pragma weak n_missing_pragma
int n_missing_pragma(void);
int (*n_missing_ptr)(int) = n_missing;
int *n_missing_dptr = &n_missing_data;
int main(void) {
    printf("%d %d %d %d\n", n_weak_alone(2), c_weak_alone(2),
           n_weak_overridden(1), c_weak_overridden(1));
    printf("%d %d\n", n_wdata_overridden, c_wdata_overridden);
    printf("both weak: one definition %d\n", both_weak() == both_weak_from_c());
    printf("%d %d %d\n", n_pragma(), n_alias(2), c_alias(2));
    printf("missing: %d %d %d %d %d\n", n_missing == 0, &n_missing_data == 0,
           n_missing_pragma == 0, n_missing_ptr == 0, n_missing_dptr == 0);
    printf("%d\n", n_missing ? n_missing(1) : -1);
    int (*f)(int) = n_missing;
    void *volatile p = (void *)f;
    printf("address %d\n", p == 0);
    printf("%ld\n", c_probe());
    return 0;
}

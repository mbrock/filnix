/* The clang side of weak-symbols.c. */
#include "weak-symbols.h"
__attribute__((weak)) int c_weak_alone(int x) { return x * 3; }
int n_weak_overridden(int x) { return x + 1000; }
__attribute__((weak)) int c_weak_overridden(int x) { return -x; }
int n_wdata_overridden = 77;
__attribute__((weak)) int c_wdata_overridden = 11;
__attribute__((weak)) int both_weak(void) { return 2; }
int both_weak_from_c(void) { return both_weak(); }
static int c_real(int x) { return x * 5; }
#pragma weak c_alias = c_real_pub
int c_real_pub(int x) { return c_real(x); }
extern int c_missing(int) __attribute__((weak));
extern int c_missing_data __attribute__((weak));
extern int n_strong_for_c(int) __attribute__((weak));
int (*c_missing_ptr)(int) = c_missing;
long c_probe(void) {
    long s = 0;
    s = s * 10 + (c_missing == 0);
    s = s * 10 + (&c_missing_data == 0);
    s = s * 10 + (c_missing_ptr == 0);
    s = s * 10 + (n_strong_for_c != 0);
    s = s * 1000 + (n_strong_for_c ? n_strong_for_c(4) : -1);
    s = s * 1000 + n_weak_alone(2) + n_weak_overridden(1) % 100;
    s = s * 100 + c_wdata_overridden + n_wdata_overridden;
    return s * 100 + n_pragma() + n_alias(3);
}

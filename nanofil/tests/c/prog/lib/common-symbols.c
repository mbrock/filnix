#include "common-symbols.h"
int shared __attribute__((common));
int (*hook)(int) __attribute__((common));
int later __attribute__((common));
long overridden = 99;
static int thrice(int x) { return 3 * x; }
void companion_set(void) { shared += 1; if (hook) hook = thrice; later *= 10; }
int companion_same(int *s, int *l, long *o) {
    return s == &shared && l == &later && o == &overridden;
}

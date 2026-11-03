// Scheduled checks (docs/schedule.md) count offsets only well inside the
// signed range: a + (2^63-4) + (2^63-4) is a - 8 (Fil-C wraps pointer
// arithmetic), not a + 2^64 - 8, so on the c arm nothing past a + 8 is
// needed and the read of a[0, 8) must not be widened to a[0, 16). No
// build traps (a review's counterexample, November 2026).
#include <stdlib.h>
#include <stdio.h>
__attribute__((noinline)) long f(int c, char *a) {
  long x = *(long *)a;
  if (c) {
    char *w = a + 0x7ffffffffffffffcL;
    w = w + 0x7ffffffffffffffcL;
    x += *(long *)w;
  } else
    x += *(long *)(a + 8);
  return x;
}
int main(void) {
  char *p = calloc(1, 16);
  printf("%ld\n", f(1, p + 8));
  return 0;
}

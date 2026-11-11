// A helper with its own specification, called in a loop, with memory
// read after each call: next_l is strchr for 'l', and count_l walks a
// string by next_l from just past each hit, reading the byte it lands
// on. Proved through the Iris program logic, the helper by a triple
// its caller uses at both of its calls: rocq/theories/programs/CountLogic.v.
#include <string.h>

/* The first 'l' in s, or null. */
__attribute__((noinline)) const char *next_l(const char *s) {
  return strchr(s, 'l');
}

/* The number of 'l's in s, found by next_l from just past each. */
int count_l(const char *s) {
  int n = 0;
  for (const char *q = next_l(s); q; q = next_l(q + 1))
    n += q[0] == 'l';
  return n;
}

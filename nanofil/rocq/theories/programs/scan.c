// A program that reads memory after libc calls: the length of its
// string, the first 'l' in it by strchr, the rest printed by puts, then
// the byte after that 'l' read through strchr's pointer. Proved through
// the Iris program logic with the libc contracts: rocq/theories/programs/ScanLogic.v.
#include <stdio.h>
#include <string.h>

/* Print s from its first 'l', then return its length plus the byte
   after that 'l'; 0 if s has no 'l'. */
int scan(const char *s) {
  size_t n = strlen(s);
  const char *q = strchr(s, 'l');
  if (!q)
    return 0;
  puts(q);
  return (int)n + q[1];
}

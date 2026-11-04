#include <stdio.h>
#include "rep.h"

int main(void) {
  struct rep r;
  r.u.s.size = 36;
  memcpy(r.u.s.data, "../build-result.cc", 19);
  struct rep copy = r;
  printf("%s\n", copy.u.s.data);
  return 0;
}

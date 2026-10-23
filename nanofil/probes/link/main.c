#include <stdio.h>
long add2(long, long);
int main(void) {
  long (*volatile fp)(long, long) = add2;   /* indirect: getter + FO checks */
  printf("direct %ld indirect %ld\n", add2(40, 2), fp(1000, 337)); fflush(stdout);
  long (*bad)(long) = (long (*)(long))add2; /* wrong signature: generic path */
  printf("generic %ld\n", bad(7));
  return 0;
}

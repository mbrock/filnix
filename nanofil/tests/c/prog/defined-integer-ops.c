/* Integer operations C leaves undefined that Fil-C defines since deluge
   (KillUB, upstream 2de132744209; docs/ub.md). Division is total: x / 0
   and x % 0 are 0, signed MIN / -1 is MIN and MIN % -1 is 0, at both
   widths, signed and unsigned; nanofil's idiv and div raised SIGFPE.
   clz and ctz of 0 are the width; nanofil's 32-bit ctz of 0 was 64.
   Shift counts are masked. Expected, by hand: (1) 0 0
   (3) -2147483648 0 (5) -7 0 (6) -3 -1 -3 1 (7) 0 0 0
   (8) -9223372036854775808 0 0 0 (9) 0 0 0 (10) 32 32 64 64 (11) 2 2. */
#include <stdio.h>
#include <limits.h>
static int g(int x){ __asm__("" : "+r"(x)); return x; }
static long gl(long x){ __asm__("" : "+r"(x)); return x; }
int main(void){
  int x=g(1), y=g(0);
  printf("(1) %d (2) %d\n", x/y, x%y);
  x=g(INT_MIN); y=g(-1);
  printf("(3) %d (4) %d\n", x/y, x%y);
  printf("(5) %d %d\n", g(7)/g(-1), g(7)%g(-1));
  printf("(6) %d %d %d %d\n", g(-7)/g(2), g(-7)%g(2), g(7)/g(-2), g(7)%g(-2));
  unsigned u=g(5), z=g(0);
  printf("(7) %u %u %u\n", u/z, u%z, u/(unsigned)g(-1));
  long a=gl(LONG_MIN), b=gl(-1), c=gl(0);
  printf("(8) %ld %ld %ld %ld\n", a/b, a%b, a/c, a%c);
  unsigned long ul=gl(-3);
  printf("(9) %lu %lu %lu\n", ul/(unsigned long)gl(0), ul%(unsigned long)gl(0), ul/(unsigned long)gl(-1));
  printf("(10) %d %d %d %d\n", __builtin_clz(g(0)), __builtin_ctz(g(0)),
         __builtin_clzl(gl(0)), __builtin_ctzl(gl(0)));
  printf("(11) %d %d\n", g(1) << g(33), (int)(gl(1) << gl(65)));
  return 0;
}

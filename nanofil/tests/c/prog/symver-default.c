/* Default symbol versions export an unversioned IR alias. Compatibility
   versions must not replace the separate unversioned implementation.
   The repeated default directive also tests alias coalescing. */
// run: $probe 0
// run: $probe 5
#include <stdio.h>

int current(int x) { return x + 13; }
int api(int);
__asm__(".symver current, api@@GLIBC_2.2.5");
__asm__(".symver current, api@@GLIBC_2.2.5");

int old_compat(int x) { return x + 3; }
__asm__(".symver old_compat, compat@GLIBC_2.2.5");
int compat(int x) { return x + 29; }

int probe(int x) { return api(x) * 100 + compat(x); }
int main(void) { printf("%d\n", probe(5)); return 0; }

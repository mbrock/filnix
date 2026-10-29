// asm-lines: \.symver
/* Top-level asm: .symver versions the getter of the local name, as
   filcc's module asm does (c_lower c_toplevel_asm/2), and blank asm is
   nothing (libressl's LCRYPTO_ALIAS as asm("")). xz and libapparmor
   version their compatibility symbols this way. */
#include <stdio.h>
int f_new(int x) { return x + 1; }
int f_old(int x) { return x + 2; }
__asm__(".symver f_old,f@VERS_1");
__asm__("\n  .symver f_new, f@@VERS_2 \n");
__asm__("");
int main(void) { printf("%d %d\n", f_new(1), f_old(1)); return 0; }

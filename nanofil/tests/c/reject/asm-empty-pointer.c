// error: an asm operand must have integer or floating type
/* "=r" on a pointer would have the asm make up its capability: refused
   ("+r" gives the pointer back, prog/asm-empty.c). */
int f(int *p) { __asm__("" : "=r"(p)); return *p; }

// error: inline asm "nop" is not supported
int f(void) { asm("nop"); return 0; }

// error: label addresses are not supported
int f(void) { void *p = &&out; out: return 0; }

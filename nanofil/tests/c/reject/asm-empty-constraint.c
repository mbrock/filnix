// error: the asm output constraint "=a" is not supported
int f(int k) { asm volatile("" : "=a"(k)); return k; }

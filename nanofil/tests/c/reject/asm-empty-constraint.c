// error: the asm output constraint "=m" is not supported
int f(int k) { asm volatile("" : "=m"(k)); return k; }

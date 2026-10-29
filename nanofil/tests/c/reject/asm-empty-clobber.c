// error: an asm clobber other than "memory" or "cc" is not supported (rax)
int f(int k) { asm volatile("" : "+r"(k) :: "rax"); return k; }

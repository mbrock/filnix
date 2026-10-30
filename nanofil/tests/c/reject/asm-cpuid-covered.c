// error: :6: inline asm "xorl %%ecx,%%ecx
/* filcc passes this through: the xorl's ecx and flags and every register cpuid
   writes are covered. nanofil cannot run it, so it refuses it at compile
   time rather than trap where filcc runs. */
unsigned f(void) { unsigned a, b, c, d;
    __asm__ volatile ("xorl %%ecx,%%ecx\ncpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : : "cc");
    return a + b + c + d; }

// error: :6: inline asm "addl $1, %%eax
/* filcc refuses the int3, but only after validating the addl, which
   nanofil does not model: it cannot prove the run-time reason, so it
   refuses at compile time. */
unsigned f(unsigned a) {
    __asm__ volatile ("addl $1, %%eax\nint3" : "+a"(a));
    return a; }

// error: inline asm "cpuid" is not supported: nanofil cannot check its instructions
/* filcc passes this cpuid through, but its "=S" output is a register
   cpuid does not write, untied, so its value would be whatever the
   register held: B1 cannot express it (docs/asm-fixed.md). */
int main(void) {
    unsigned a, b, c, d, s;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d), "=S"(s) : "a"(0));
    return (int)(a + b + c + d + s) & 0;
}

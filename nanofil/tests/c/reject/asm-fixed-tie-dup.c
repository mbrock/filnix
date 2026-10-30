// error: inline asm "cpuid" is not supported
/* An input tied to the eax output and another input in eax name one
   register twice; clang's Fil-C crashes on it, so it is refused. */
unsigned f(void) {
    unsigned a, b, c, d;
    __asm__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "0"(0), "a"(1));
    return a;
}

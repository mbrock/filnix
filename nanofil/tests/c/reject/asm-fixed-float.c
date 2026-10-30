// error: inline asm "cpuid" is not supported
/* B1's operands are integers: a float in eax is not one. */
float f(void) {
    float a; unsigned b, c, d;
    __asm__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(0));
    return a;
}

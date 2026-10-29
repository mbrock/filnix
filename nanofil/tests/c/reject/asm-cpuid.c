// error: inline asm "cpuid" is not supported: nanofil cannot check its instructions
/* filcc's validator accepts cpuid when its outputs cover eax, ebx, ecx
   and edx, and passes it through; nanofil cannot check an instruction,
   so it refuses rather than trap where filcc runs. */
int main(void) {
    unsigned a, b, c, d;
    __asm__ volatile ("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d) : "a"(0));
    return (int)(a + b + c + d) & 0;
}

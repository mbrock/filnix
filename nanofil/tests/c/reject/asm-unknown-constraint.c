// error: inline asm "rdtsc" is not supported: nanofil cannot check its instructions
/* A constraint whose lowering by clang nanofil does not know (x86's A,
   the edx:eax pair) leaves filcc's reason uncertain, so nanofil refuses
   the asm at compile time rather than guess (c_lower
   asm_known_constraint/1). */
int main(void) {
    unsigned long long t;
    __asm__ volatile ("rdtsc" : "=A"(t));
    return (int)(t & 0);
}

/* An asm whose template is blank (spaces, tabs or newlines) emits no
   instruction; filcc passes it through when no operand is a pointer.
   libgcrypt's CT_DEOPTIMIZE_VAR (asm volatile("\n" : "+r"(var) ::
   "memory")) and xxhash's XXH_COMPILER_GUARD (__asm__("" : "+r"(v)))
   hide a value from the optimizer; "=r" writes an unspecified value;
   "i" and "r" inputs are only read. Before, nanofil refused all of
   these but the operand-less barrier. */
#include <stdio.h>

static unsigned long mask_for(unsigned long op) {
    unsigned long mask = -op;
    asm volatile ("\n" : "+r" (mask) :: "memory");
    return mask;
}

static unsigned guard(unsigned v) { __asm__("" : "+r"(v)); return v * 2; }
static double dguard(double d) { __asm__ __volatile__("\t" : "+g"(d) :: "memory", "cc"); return d + 1; }

static int counter;
static int bump(void) { return ++counter; }

int main(void) {
    int k = 3, junk = 0;
    __asm__ volatile("" : : "r"(k), "i"(5), "n"(sizeof(int)), "g"(bump()));
    __asm__ volatile("" : "=r"(junk));          /* unspecified: not printed */
    (void)junk;
    unsigned long a = 0x1234, b = 0x5678;
    unsigned long sel = (mask_for(1) & a) | (~mask_for(1) & b);
    printf("%u %g %d %lx %lx\n", guard(21), dguard(1.5), counter, sel,
           (mask_for(0) & a) | (~mask_for(0) & b));
    return 0;
}

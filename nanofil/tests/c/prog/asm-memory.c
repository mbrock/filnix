/* An asm with a memory operand, as gnulib's fpucw.h reads and sets the
   x87 control word around long double printf: clang's Fil-C compiles
   it to a run-time error, so a program that never runs it works
   (docs/abi-findings.md, *Inline asm*). This one never does. */
#include <stdio.h>
typedef unsigned short fpucw_t;
static fpucw_t get_cw(void) {
    fpucw_t cw;
    __asm__ __volatile__("fnstcw %0" : "=m"(*&cw));
    return cw;
}
static void set_cw(fpucw_t cw) { __asm__ __volatile__("fldcw %0" : : "m"(*&cw)); }
int main(int argc, char **argv) {
    (void)argv;
    if (argc > 5) set_cw((fpucw_t)(get_cw() | 0x300));
    printf("%.3Lf\n", 1.0L / 3);
    return 0;
}

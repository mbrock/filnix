// reference-opt: -O0
// trap-reason
/* Calls through a declaration without a prototype to a function this
   translation unit defines with other parameters (gmp's configure probe
   calls `void g(){}` with six arguments). C11 6.5.2.2p6 makes such a
   call undefined only when it runs; clang compiles it, and filcc -O0
   passes every argument and lets the callee read the ones it declares:
   extra arguments are ignored, and reading one that was not passed
   traps. filcc -O2 inlines h(5) and prints a value, so the reference is
   -O0. */
#include <stdio.h>
#include <string.h>

void g() { puts("g"); }
int h(a, b) int a, b; { return a + b; }
int k();
static double d();

int main(int argc, char **argv) {
    g(1, argv, 3L, argv, argv, 2);
    printf("%d\n", h(2, 3, 4));
    printf("%d\n", k(7, 8));
    printf("%g\n", d(1.5, 2));
    int (*p)() = h;
    printf("%d\n", p(10, 20, 30));
    fflush(stdout);
    if (argc > 0) printf("%d\n", h(5));
    return 0;
}
int k(int a) { return a * 10; }
static double d(double x) { return x * 2; }

// link: lib/section.c
// signatures
/* GNU's section attribute, as filcc compiles it: FilPizlonator gives
   the pizlonated data object and the function no section, so they stay
   in .data, .bss, .rodata and .text and the program behaves as without
   it (CPython's _PyRuntime is in ".PyRuntime" only for debuggers).
   Objects and a function with sections, defined here by nanofil and in
   the companion by clang, are used from both sides, pointers included. */
#include <stdio.h>

int counter __attribute__((section(".mydata"))) = 41;
static const char *names[] __attribute__((section(".myrel"))) = { "alpha", "beta" };
const int table[3] __attribute__((section(".myrodata"))) = { 1, 2, 3 };
static int zeroed __attribute__((section(".mybss")));
__attribute__((section(".text.mine"))) int bump(int k) { zeroed += k; return ++counter + zeroed; }

extern int lib_value;
extern int *lib_ptr;
int lib_call(int);

int main(void) {
    printf("%d %s %s %d\n", bump(1), names[0], names[1], table[2]);
    printf("%d %d %d\n", lib_value, *lib_ptr, lib_call(2));
    printf("%d %d\n", counter, zeroed);
    return 0;
}

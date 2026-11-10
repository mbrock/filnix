/* Fil-C's own module-asm directives, as glibc's libc-symbols.h uses
   them (FilPizlonator.cpp, compileModuleAsm): hidden_proto is
   .filc_rename N, __GI_N, so the unit's definition and uses of N are
   __GI_N; hidden_def is .filc_alias __GI_N, N, which exports N again;
   hidden_weak is .filc_weak_alias. clang (lib/filc-asm.c) calls each
   symbol by its final name, and defines __GI_ext and ext apart, so a
   use that missed its rename reads the wrong one. An alias replaces a
   weak declaration as a strong symbol: the companion, linked first,
   defines a weak wq the program's must override. An alias at offset
   0, as glibc's vtables.c makes, is the object itself.
   (An unreferenced static has no symbol left for .filc_globl to export
   at clang -O1, so the test exports a global.) */
// link: lib/filc-asm.c
// link-first
#include <stdio.h>

int foo(int);
__asm(".filc_rename foo, __GI_foo");
int foo(int x) { return x + 1; }
__asm(".filc_" "" "alias " "" "__GI_foo" ", " "" "foo");

extern int counter;
__asm(".filc_rename counter, __GI_counter");
int counter = 40;
__asm(".filc_alias __GI_counter, counter");
const int table[3] = { 1, 2, 3 };
__asm(".filc_alias " "table + " "0" ", " "table0");

int ext(void);
__asm(".filc_rename ext, __GI_ext");
__asm(".filc_rename absent, __GI_absent");

int wfn(void);
__asm(".filc_rename wfn, __GI_wfn");
int wfn(void) { return 5; }
__asm(".filc_" "weak_" "alias " "" "__GI_wfn" ", " "" "wfn");

int q(void);
int use_q(void) { return q() * 10; }
int qq(void) { return 7; }
__asm(".filc_alias qq, q");
extern int wq(void) __attribute__((weak));
int use_wq(void) { return wq ? wq() : -1; }
int wqq(void) { return 8; }
__asm(".filc_alias wqq, wq");

int r0(void) { return 3; }
extern int r1(void) __attribute__((alias("r0")));
__asm(".filc_rename r0, __GI_r0");

/* glibc's versioned functions: a C alias, then a .filc_alias of the
   same pair, which FilPizlonator coalesces with it. */
int r2(void);
__asm(".filc_rename r2, __GI_r2");
int r3(void) { return 13; }
extern int r2(void) __attribute__((alias("r3")));
__asm(".filc_alias r3, __GI_r2");

int shown(void) { return 9; }
__asm(".filc_globl shown");
int soft(void) { return 11; }
__asm(".filc_weak soft");

int from_clang(void);

int main(void)
{
    printf("%d %d %d\n", foo(1), counter, ext());
    printf("%d %d %d %d\n", wfn(), use_q(), r1(), shown());
    printf("%d %d\n", use_wq(), r2());
    printf("%d\n", from_clang());
    return 0;
}

/* A declaration attribute written among a pointer's qualifiers is the
   declaration's, as clang applies it (ProcessDeclAttributes) and as
   glibc writes `int *__attribute__((weak, __const__))
   __h_errno_location (void)` and malloc's hooks. The companion
   (lib/attr-slide.c) defines pick and hook strongly, so the weak
   definitions here give way to them, and absent stays a weak
   undefined function, null. A section on a function is kept as filcc
   keeps it, in .text. */
// link: lib/attr-slide.c
#include <stdio.h>

int *__attribute__((weak)) pick(void) { static int one = 1; return &one; }
void *__attribute__((weak)) (*hook)(int) = 0;
extern int *__attribute__((weak, __const__)) absent(void);
void *__attribute__((section(".text.compat"))) compat(int x) { return x ? &x : 0; }

int main(void)
{
    printf("%d %d %d %d\n", *pick(), hook != 0 && hook(3) == 0, absent == 0,
           compat(0) == 0);
    return 0;
}

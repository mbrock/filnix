// cflags: -std=gnu90 -O2
// link: lib/gnu89-inline-only.c
/* A GNU extern inline body that no unit defines out of line, as glibc's
   __libc_use_alloca and __find_specmb are: clang inlines its calls at
   -O2, so nanofil's calls go to a local copy. A wrapper that calls its
   own external definition through an asm label, as glibc's fortify
   wrappers do, keeps calling the companion's definition. */
#include <stdio.h>
extern inline int nowhere(int x) { return 3 * x + 1; }
extern inline int twice_nowhere(int x) { return nowhere(nowhere(x)); }
extern int wrapped_real(int, int) __asm__("wrapped");
extern inline int wrapped(int a, int b) { return wrapped_real(a, b) + 1; }
int main(void)
{
    printf("%d %d %d\n", nowhere(4), twice_nowhere(2), wrapped(3, 4));
    return 0;
}

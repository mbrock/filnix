/* An always_inline body that is not the external definition (a C99
   inline-only definition) is inlined by clang at
   every call once it optimizes, so no unit defines the symbol: ell's
   DEFINE_CLEANUP_FUNC. nanofil calls a local copy. (filcc -O0 leaves
   the calls and fails to link.) glibc's fortify wrappers are GNU extern
   inline always_inline bodies that call the external function through
   an asm label; they keep calling it (a copy would call itself). */
// cflags: -O2 -D_FORTIFY_SOURCE=2
#include <stdio.h>
#include <stdlib.h>
#define DEFINE_CLEANUP_FUNC(func) \
    inline __attribute__((always_inline)) void _l_ ## func ## _cleanup(void *p) { func(*(void **) p); }
static int freed;
static void my_free(void *p) { freed++; free(p); }
DEFINE_CLEANUP_FUNC(my_free)
inline __attribute__((always_inline)) int fact(int n) { return n < 2 ? 1 : n; }
int main(void)
{
    {
        __attribute__((cleanup(_l_my_free_cleanup))) char *s = malloc(4);
        s[0] = 0;
    }
    char *root = realpath("/", NULL);
    printf("%d %d %d %s\n", freed, fact(21), fact(5), root);
    free(root);
    return 0;
}

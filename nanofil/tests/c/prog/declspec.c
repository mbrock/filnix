// cflags: -fdeclspec
/* clang's __declspec, with -fdeclspec as ruby's configure adds it:
   ruby's headers prefer __declspec(noreturn) and __declspec(noinline)
   when __has_declspec_attribute says so. align(N) is aligned(N). */
#include <stdio.h>
#include <stdlib.h>

__declspec(noreturn) static void fail(const char *m) { puts(m); exit(3); }
__declspec(noinline) static int twice(int x) { return 2 * x; }
__declspec(deprecated) int old(void);
int old(void) { return 1; }

struct s {
    char c;
    __declspec(align(32)) int x;
};
static __declspec(align(64)) char buf[8];

int main(int argc, char **argv)
{
    (void)argv;
    struct s v = {1, 2};
    printf("%zu %zu %d %d %d\n", sizeof v, _Alignof(struct s), twice(v.x), old(),
           (int)((unsigned long)buf % 64));
    if (argc > 0)
        fail("bye");
    return 0;
}

/* Under clang, glibc's _FORTIFY_SOURCE printf family are static
   overloadable wrappers whose pass_object_size parameter clang prefers
   at every call, mangled as functions of their own. A program that
   defines dprintf itself (cyrus-sasl's sample/common.c) keeps its
   definition, but its direct calls still reach the wrapper, so libc's
   dprintf writes to the fd; a pointer to dprintf reaches the program's. */
// cflags: -O2 -D_FORTIFY_SOURCE=2
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
static int debuglevel = 1;
int dprintf(int lvl, const char *fmt, ...);
int main(void)
{
    char b[16];
    int n = sprintf(b, "%d-%s", 42, "x");
    snprintf(b + n, sizeof b - n, "!%d", 7);
    printf("%s %zu\n", b, strlen(b));
    fprintf(stdout, "%d\n", dprintf(1, "lvl %d\n", 1));
    int (*own)(int, const char *, ...) = dprintf;
    printf("via pointer %d\n", own(1, "own %d\n", 2));
    fflush(stdout);
    return dprintf(2, "hidden\n");
}
int dprintf(int lvl, const char *fmt, ...)
{
    va_list ap; int ret = 0;
    if (debuglevel >= lvl) { va_start(ap, fmt); ret = vfprintf(stdout, fmt, ap); va_end(ap); }
    return ret;
}

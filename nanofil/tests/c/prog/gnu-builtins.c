/* __builtin_memcpy, memmove and memset are the library functions; lz4
   calls them so. __builtin_assume_aligned(p, a[, offset]) is p, as a
   void * (xz's tuklib_integer.h): the promise changes nothing in
   Fil-C, whose bounds stay p's. The last copy overruns its destination:
   both builds trap there. */
#include <stdio.h>
#include <string.h>

int main(void)
{
    char a[8] = "abcdefg", b[8];
    __builtin_memset(b, 'x', 7);
    b[7] = 0;
    __builtin_memcpy(b, a, 3);
    __builtin_memmove(b + 1, b, 4);
    printf("%s\n", b);
    const char *q = __builtin_assume_aligned(a + 2, 2, 0);
    long *w = __builtin_assume_aligned((long *)b, 8);
    printf("%c %d\n", q[1], (char *)w == b);
    fflush(stdout);
    __builtin_memcpy(b + 4, a, 5);
    printf("%s\n", b);
    return 0;
}

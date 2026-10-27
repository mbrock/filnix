/* __builtin_memcpy, memmove and memset are the library functions; lz4
   calls them so. The last copy overruns its destination: both builds
   trap there. */
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
    fflush(stdout);
    __builtin_memcpy(b + 4, a, 5);
    printf("%s\n", b);
    return 0;
}

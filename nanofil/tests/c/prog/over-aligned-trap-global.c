/* The byte below an aligned(64) global is out of bounds, as under
   filcc, though the pad before its header is there. */
#include <stdio.h>
char g[8] __attribute__((aligned(64))) = "abc";
int main(void)
{
    char *volatile p = g;
    volatile int k = -1;
    printf("%c\n", p[0]);
    return p[k];
}

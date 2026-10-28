/* An object aligned above 16 starts at its payload: the byte below an
   aligned(64) local is out of bounds, as under filcc, though its
   allocation's padding is there. */
#include <stdio.h>
int main(void)
{
    char buf[8] __attribute__((aligned(64))) = "abc";
    char *volatile p = buf;
    volatile int k = -1;
    printf("%c\n", p[0]);
    return p[k];
}

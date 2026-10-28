// cflags: -std=gnu89
/* In GNU89 a K&R parameter without a declaration is int. */
#include <stdio.h>
int twice(x) { return x * 2; }
int pick(s, i) char *s; { return s[i]; }
int main(void)
{
    printf("%d %d\n", twice(21), pick("xyz", 2));
    return 0;
}

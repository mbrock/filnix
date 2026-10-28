// cflags: -std=gnu90 -O2
// link: lib/gnu89-inline.c
/* GNU89 inline (-std=gnu90, c90, -fgnu89-inline): an extern inline body
   is never the external definition, which the companion holds (as libc
   holds atoi's, whose glibc header body is extern __inline under -O2),
   while a plain inline body is one, which the companion calls. */
#include <stdio.h>
#include <stdlib.h>
extern inline int twice(int x) { return 2 * x; }
inline int plain(int x) { return x + 1; }
int call_twice(int);
int call_plain(int);
int main(void)
{
    printf("%d %d %d %d\n", twice(3), call_twice(4), call_plain(5), atoi("42"));
    return 0;
}

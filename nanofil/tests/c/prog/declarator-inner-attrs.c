/* An attribute may begin a parenthesized declarator, before its '*':
   emacs' dynlib.h has typedef void (ATTRIBUTE_MAY_ALIAS *dynlib_function_ptr) (void);. */
#include <stdio.h>

#define MAY_ALIAS __attribute__((__may_alias__))

typedef void (MAY_ALIAS *fptr)(void);
static int (__attribute__((unused)) *table[2])(int);

static void hi(void) { puts("hi"); }
static int twice(int x) { return 2 * x; }

int main(void)
{
    fptr f = hi;
    f();
    table[1] = twice;
    printf("%d %d\n", table[0] == 0, table[1](21));
    return 0;
}

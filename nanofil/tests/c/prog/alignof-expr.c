/* GNU __alignof__ of an expression, as glibc's strcoll_l asserts
   __alignof__ (table[0]): a named object's alignment is its
   declaration's, with its aligned and _Alignas requests, and any other
   operand's is its type's. The operand is not evaluated. Constant uses
   (an array bound, a case label, a static initializer) fold. */
#include <stdio.h>
#include <stdint.h>

struct s { char c; double d; };
static long double ld;
static char plain;
static char wide __attribute__((aligned(32)));
static _Alignas(16) int boxed[3];
static const int32_t *table;
static unsigned long folded[] = { __alignof__ (ld), __alignof__ (wide), __alignof__ (boxed) };

int main(void)
{
    struct s v, *p = &v;
    short arr[5];
    int n = 7, i = 0;
    double vla[n];
    char local __attribute__((aligned(8)));
    char bound[__alignof__ (*p)];
    switch (__alignof__ (table[0])) { case __alignof__ (int): i = 1; break; default: i = 2; }
    unsigned long r[] = {
        __alignof__ (table[0]), __alignof__ (*table), __alignof__ table,
        __alignof__ (v), __alignof__ (*p), __alignof__ (arr), __alignof__ (arr[1]),
        __alignof__ (vla), __alignof__ (local), __alignof__ (plain),
        __alignof__ (n++), __alignof__ (ld + 1), __alignof__ ((char) n),
        _Alignof (vla[0]), sizeof bound,
    };
    for (unsigned k = 0; k < sizeof r / sizeof r[0]; k++) printf("%lu ", r[k]);
    printf("\n%lu %lu %lu n=%d i=%d %d\n", folded[0], folded[1], folded[2], n, i,
           (int) (((uintptr_t) &wide) % __alignof__ (wide)));
    return 0;
}

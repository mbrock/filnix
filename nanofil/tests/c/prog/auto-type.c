/* GNU __auto_type: the type of the initializer after lvalue conversion
   and decay (no promotion), so const is dropped, an array becomes a
   pointer and a char stays a char; the initializer runs once. ell's
   L_IN_SET writes const __auto_type __v = (val). */
#include <stdio.h>
static int calls;
static int next(void) { return ++calls; }
static int f(int x) { return x + 1; }
__auto_type gl = 3000000000;
int main(void)
{
    __auto_type a = 5;
    const __auto_type b = 2L;
    char c = 'x';
    __auto_type cc = c;
    int arr[4] = {1, 2, 3, 4};
    __auto_type p = arr;
    __auto_type fp = f;
    const int ci = 9;
    __auto_type nc = ci;
    nc++;
    __auto_type n = next();
    _Bool same = __builtin_types_compatible_p(__typeof__(p), int *);
    printf("%zu %zu %zu %zu %zu %d %d %d %d %d %d\n", sizeof a, sizeof b, sizeof cc, sizeof p,
           sizeof gl, same, p[3], fp(1), nc, n, calls);
    return 0;
}

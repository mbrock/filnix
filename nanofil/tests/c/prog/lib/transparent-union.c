/* The clang side of transparent-union.c. */
#include "transparent-union.h"

long c_ptr(PtrArg a) { return a.ip ? *a.ip : -1; }
long c_word(WordArg w) { return w.n * 3; }
int c_int(union IntArg a) { return a.i + 1; }
long c_mixed(Mixed m) { return m.l * 2; }

long c_calls(void)
{
    static int i = 40;
    static long l = 50;
    Mixed m;
    m.l = 9;
    return n_ptr(&i) + n_ptr(&l) * 10 + n_ptr((int *)0) * 100 + n_word(77L)
        + n_int(5) + n_int(6u) + n_mixed(m);
}

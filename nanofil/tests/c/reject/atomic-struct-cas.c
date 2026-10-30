// error: __c11_atomic_compare_exchange_strong
/* clang leaves *expected unchanged when a compare-exchange of a struct
   smaller than its atomic size fails (7.17.7.4p2 says it gets the
   current value), so nanofil refuses it rather than differ from filcc
   or copy the bug. */
#include <stdatomic.h>
typedef struct { char a, b, c; } t3;
_Atomic(t3) g;
int f(t3 *e, t3 n) { return atomic_compare_exchange_strong(&g, e, n); }

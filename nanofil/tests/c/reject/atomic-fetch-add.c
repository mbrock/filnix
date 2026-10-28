// error: __c11_atomic_fetch_add is an atomic read-modify-write
#include <stdatomic.h>
atomic_int refs;
int take(void) { return atomic_fetch_add(&refs, 1); }

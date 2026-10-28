// error: __c11_atomic_fetch_add needs a pointer to an integer
_Atomic double d;
double add(void) { return __c11_atomic_fetch_add(&d, 1.0, __ATOMIC_SEQ_CST); }

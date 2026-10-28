// error: __c11_atomic_load needs a pointer to an _Atomic
int plain;
int get(void) { return __c11_atomic_load(&plain, __ATOMIC_SEQ_CST); }

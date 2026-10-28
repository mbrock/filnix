// error: __atomic_fetch_add needs a pointer to an integer (an _Atomic one for __c11 builtins), or to a pointer to exchange, compare it or (__c11) add to it
/* GCC's builtin adds to a pointer unscaled; filcc's clang breaks its
   module on it ("atomicrmw add operand must have integer type"). */
int *gp;
int *bump(void) { return __atomic_fetch_add(&gp, 4, __ATOMIC_SEQ_CST); }

// error: static assertion failed
// C11 6.7.10: a static assertion among struct members, here as gnulib's
// verify_expr writes it inside sizeof.
int f(void) { return sizeof(struct { _Static_assert(1 == 2, "no"); int x; }); }

// error: goto into a statement expression is not allowed
int f(void) { ({ goto inner; }); return ({ inner: 1; }); }

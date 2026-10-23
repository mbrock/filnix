// error: cannot assign ptr(int) to long
long h(long);
long f(int *p) { return h(p); }

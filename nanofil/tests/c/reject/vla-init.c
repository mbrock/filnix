// error: a variable length array cannot be initialized
int f(int n) { int a[n] = {0}; return a[0]; }

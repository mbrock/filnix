// error: variably modified types
int f(int n, int (*a)[n]) { int (*p)[n] = a; return sizeof *p; }

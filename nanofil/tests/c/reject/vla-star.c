// error: [*] is allowed only in a function prototype
int f(int n) { int (*p)[*] = 0; return p == 0; }

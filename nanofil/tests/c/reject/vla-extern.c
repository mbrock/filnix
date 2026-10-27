// error: p has a variably modified type at file scope or with linkage
int f(int n) { extern int (*p)[n]; return p != 0; }

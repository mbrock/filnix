// error: goto into the scope of a variably modified identifier
int f(int n) { if (n) goto in; int (*p)[n] = 0; in: return p == 0; }

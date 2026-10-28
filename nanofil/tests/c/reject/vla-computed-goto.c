// error: goto into the scope of a variably modified identifier
int f(int n) { void *p = &&in; goto *p; { int a[n]; in: a[0] = 1; return a[0]; } }

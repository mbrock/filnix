// error: goto into the scope of a variably modified identifier
int f(int n) { goto in; { int a[n]; in: a[0] = 1; return a[0]; } }

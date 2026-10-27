// error: a range designator's initializer has side effects
int f(int x) { int a[3] = { [0 ... 2] = x++ }; return a[0] + x; }

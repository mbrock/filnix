// error: variably modified member
int f(int n) { struct s { int a[n]; } x; return sizeof x; }

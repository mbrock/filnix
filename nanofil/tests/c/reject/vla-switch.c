// error: switch jumps into the scope of a variably modified identifier
int f(int n) { switch (n) { case 0: ; int a[n]; case 1: return 1; } return 0; }

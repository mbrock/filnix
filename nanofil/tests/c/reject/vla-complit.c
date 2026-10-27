// error: a compound literal cannot have a variable length array type
int f(int n) { return ((int[n]){0})[0]; }

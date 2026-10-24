// error: invalid bit-field
struct s { int a : 33; };
int f(void) { struct s v; return 0; }

// error: bitfields
struct s { int a : 3; };
int f(void) { struct s v; return 0; }

// error: cannot convert struct(0) to int
struct S { int a; } s;
unsigned long f(void) { return sizeof((int)s); }

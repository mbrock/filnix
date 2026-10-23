// error: invalid operand to not
struct S { int a; } s;
unsigned long f(void) { return sizeof(!s); }

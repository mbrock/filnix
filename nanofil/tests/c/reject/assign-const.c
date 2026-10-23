// error: assignment to a read-only lvalue
struct S { int b[2]; };
const struct S cs;
void f(void) { cs.b[0] = 1; }

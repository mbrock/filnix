// error: assignment to a non-lvalue
struct S { int a; };
struct S g(void);
void f(void) { g().a = 1; }

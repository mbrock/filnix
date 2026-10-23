// error: & of a non-lvalue
struct S { int a; };
struct S g(void);
int *f(void) { return &g().a; }

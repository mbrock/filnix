// error: assignment to a read-only lvalue
struct K { int n; struct { const int id; } inner; };
void f(struct K *a, struct K *b) { *a = *b; }

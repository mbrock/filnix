// error: postinc of a read-only lvalue
void f(const int *p) { (*p)++; }

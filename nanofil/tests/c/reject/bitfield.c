// error: cannot take the address of a bit-field
struct s { int a : 3; };
int *f(struct s *p) { return &p->a; }

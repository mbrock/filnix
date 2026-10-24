// error: sizeof of a bit-field
struct s { int a : 3; };
unsigned long f(struct s *p) { return sizeof p->a; }

// error: packed pointers
struct __attribute__((packed)) s { char c; int *p; };
int f(struct s *v) { return *v->p; }

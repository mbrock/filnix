// error: packed bit-fields
struct [[gnu::packed]] s { char c; int x : 3; };
int f(struct s *v) { return v->x; }

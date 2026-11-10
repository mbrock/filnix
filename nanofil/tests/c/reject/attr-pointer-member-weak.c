// error: attribute weak is not supported in this position
// A member has no symbol of its own, so a declaration attribute among
// its pointer's qualifiers has nowhere to go (clang ignores it).
struct s { int *__attribute__((weak)) p; };
int g(struct s *x) { return x->p != 0; }

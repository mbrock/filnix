// error: a packed bit-field that no access of its type covers
// The struct is 2 bytes, so no 8-byte long access within it holds x.
// A type no wider than int is accessed in a narrower integer, as clang
// does (prog/packed-bitfield-narrow.c); a wider one, whose value keeps
// its type, is refused.
struct [[gnu::packed]] s { char c; long x : 3; };
int f(struct s *v) { return v->x; }

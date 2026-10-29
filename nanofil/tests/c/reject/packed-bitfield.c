// error: a packed bit-field that no access of its type covers
// The struct is 2 bytes, so no 4-byte int access within it holds x
// (clang loads it as an i8); prog/packed-bitfields.c has the ones that fit.
struct [[gnu::packed]] s { char c; int x : 3; };
int f(struct s *v) { return v->x; }

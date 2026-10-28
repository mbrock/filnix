// error: vector types
typedef int v4si __attribute__((vector_size(16)));
struct tile { v4si t; short rows; };
static void tile_zero(struct tile *dst, struct tile src) { dst->t = src.t; }
void f(struct tile *d, struct tile *s) { tile_zero(d, *s); }

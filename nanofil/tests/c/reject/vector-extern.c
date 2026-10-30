// error: :8: a function with external linkage or called through a pointer cannot take or return a vector
// vectors
/* filcc passes a vector in vector registers, nanofil as a struct, so
   only static functions (immintrin.h's) take or return one. */
typedef int v4si __attribute__((vector_size(16)));
v4si twice(v4si a);
static v4si thrice(v4si a) { return a * 3; }
int f(v4si *p) { return thrice(*p)[1] + twice(*p)[0]; }

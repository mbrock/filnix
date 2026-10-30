// error: :4: a function with external linkage or called through a pointer cannot take or return a vector
/* A definition with external linkage may be called by filcc's code. */
typedef float v4sf __attribute__((vector_size(16)));
v4sf half(v4sf a) { return a / 2; }

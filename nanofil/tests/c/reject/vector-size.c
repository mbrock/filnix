// error: vector types
typedef int v4si __attribute__((vector_size(16)));
int f(void) { v4si v; return sizeof v; }

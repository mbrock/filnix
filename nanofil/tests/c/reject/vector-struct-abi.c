// error: a function with external linkage or called through a pointer cannot take or return a vector
// vectors
/* A struct holding a vector is laid out at the vector's alignment in
   filcc's calls, so it cannot cross to code nanofil did not compile. */
typedef int v4si __attribute__((vector_size(16)));
struct S { int k; v4si v; };
int take(int k, struct S s, long m);
int f(void) { struct S s = {1, {2}}; return take(1, s, 2); }

// error: passing a vector to a variadic or unprototyped function is not supported
// vectors
/* filcc aligns a vector passed through ... to its own alignment, where
   nanofil would pack it at 8: the callee's va_arg reads other bytes. */
typedef int v4si __attribute__((vector_size(16)));
int vsum(int n, ...);
int f(void) { v4si s = {1, 2, 3, 4}; return vsum(1, s); }

// error: initializer is not a constant
/* A const local with a non-constant initializer hides an outer
   constant object of its name. */
static const int K = 7;
int f(int y) { const int K = y; static int v = K; return v; }

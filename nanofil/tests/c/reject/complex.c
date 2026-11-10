// error: _Complex
/* GNU's integer complex types are not supported; _Complex float and
   double are (tests/c/prog/complex.c). */
int f(void) { _Complex int z; return 0; }

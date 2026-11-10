// error: multiplying a _Complex value by a _Complex value is not supported: clang calls compiler-rt's native __muldc3
/* clang multiplies two complex values with compiler-rt's __muldc3,
   native code in Fil-C (libyolort) that checked IR cannot call. */
_Complex double f(_Complex double a, _Complex double b) { return a * b; }

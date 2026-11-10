// error: dividing by a _Complex value is not supported: clang calls compiler-rt's native __divsc3
/* Dividing by a complex value, even a real one's, is __divsc3's job. */
_Complex float f(float a, _Complex float b) { return a / b; }

// error: returning _Complex long double is not supported yet
/* A struct of two long doubles returns through memory, but clang returns
   _Complex long double as a first-class pair, so the struct shape that
   serves float and double does not serve it. Arguments are the same. */
_Complex long double f(long double x) { _Complex long double z; __real__ z = x; __imag__ z = 0; return z; }

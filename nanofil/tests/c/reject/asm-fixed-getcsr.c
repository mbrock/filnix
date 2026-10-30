// error: _mm_getcsr is not supported
/* filcc reads MXCSR; nanofil cannot express it. */
#include <immintrin.h>
unsigned f(void) { return _mm_getcsr(); }

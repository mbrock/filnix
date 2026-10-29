// error: vector types is not supported
// xz's lz_decoder.h and brotli's matching_tag_mask.h: a local of SSE2's
// __m128i, whose typedef is also aligned, names the vector type, not the
// alignment, as the reason.
#include <emmintrin.h>
void f(unsigned char *b) { const __m128i x = _mm_loadu_si128((__m128i *)b); (void)x; }

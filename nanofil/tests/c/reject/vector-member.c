// error: vector types is not supported (member i)
// no-vectors
// x264's common/x86/util.h: a union whose member i is an __m128. With GNU
// vector types off the member is refused; naming it said "no member named
// i", which the survey could not tell from a typing gap.
typedef float v4 __attribute__((vector_size(16)));
typedef union { v4 i; unsigned d[4]; } U;
void copy(void *p, void *q) { ((U *)p)->i = ((U *)q)->i; }

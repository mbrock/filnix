// error: vector types of 32 bytes
// vectors
/* Only 16-byte vectors (SSE through SSE4.2) are supported; AVX's 32-byte
   ones come later. */
typedef int v8si __attribute__((vector_size(32)));
v8si g;

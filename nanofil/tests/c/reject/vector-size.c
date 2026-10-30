// error: vector types of 64 bytes
/* Only 16- and 32-byte vectors (SSE through AVX2) are supported;
   AVX-512's 64-byte ones are not. */
typedef int v16si __attribute__((vector_size(64)));
v16si g;

/* PALIGNR's immediate is 8 bits: clang's default-error range check aside
   (progtest builds with -w), 256 is 0 and 257 is 1, on 16 and 32 bytes. */
#include <immintrin.h>
#include <stdio.h>
__attribute__((target("avx2"))) static void run(void) {
    unsigned char a[32], b[32], o[32];
    for (int i = 0; i < 32; i++) { a[i] = (unsigned char)(i + 100); b[i] = (unsigned char)i; }
    __m128i x = _mm_loadu_si128((const __m128i *)a), y = _mm_loadu_si128((const __m128i *)b);
    __m256i X = _mm256_loadu_si256((const __m256i *)a), Y = _mm256_loadu_si256((const __m256i *)b);
    _mm_storeu_si128((__m128i *)o, _mm_alignr_epi8(x, y, 256));
    for (int i = 0; i < 16; i++) printf("%d ", o[i]);
    printf("\n");
    _mm_storeu_si128((__m128i *)o, _mm_alignr_epi8(x, y, 257));
    for (int i = 0; i < 16; i++) printf("%d ", o[i]);
    printf("\n");
    _mm256_storeu_si256((__m256i *)o, _mm256_alignr_epi8(X, Y, 257));
    for (int i = 0; i < 32; i++) printf("%d ", o[i]);
    printf("\n");
}
int main(void) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx2")) { puts("skip: no avx2"); return 0; }
    run();
    return 0;
}

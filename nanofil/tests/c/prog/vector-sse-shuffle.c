/* immintrin.h's SSE through SSE4.2 intrinsics, computed element by
   element (c_lower vector_op//6): shifts by an immediate and by a
   vector's low quadword, at and above the element width; byte shifts,
   packs, shuffles, alignr and blends. Every result matches filcc's. */
#include <immintrin.h>
#include <stdio.h>
#include <string.h>
static unsigned char seed[256];
static __m128i g(int k) { return _mm_loadu_si128((const __m128i *)(seed + (k * 37) % 200)); }
static void p(const char *n, __m128i v) {
    unsigned char b[16]; _mm_storeu_si128((__m128i *)b, v);
    printf("%-22s", n); for (int i = 0; i < 16; i++) printf("%02x", b[i]); printf("\n");
}
#define T(e) p(#e, e)
#define I(e) printf("%-22s%d\n", #e, (int)(e))
int main(void) {
    unsigned x = 12345;
    for (int i = 0; i < 256; i++) { x = x * 1103515245u + 12345u; seed[i] = (unsigned char)(x >> 16); }
    seed[5] = 0x80; seed[6] = 0x7f; seed[40] = 0; seed[41] = 0xff;
    __m128i a = g(1), b = g(2), c = g(3);
    for (int sh = 0; sh < 3; sh++) {
        int s = sh == 0 ? 3 : sh == 1 ? 17 : 70;
        T(_mm_slli_epi16(a, s)); T(_mm_srli_epi16(a, s)); T(_mm_srai_epi16(a, s));
        T(_mm_slli_epi32(a, s)); T(_mm_srli_epi32(a, s)); T(_mm_srai_epi32(a, s));
        T(_mm_slli_epi64(a, s)); T(_mm_srli_epi64(a, s));
        __m128i cnt = _mm_cvtsi32_si128(s);
        T(_mm_sll_epi16(a, cnt)); T(_mm_srl_epi32(a, cnt)); T(_mm_sra_epi16(a, cnt)); T(_mm_sll_epi64(a, cnt));
    }
    T(_mm_slli_si128(a, 3)); T(_mm_srli_si128(a, 5)); T(_mm_bslli_si128(a, 15)); T(_mm_srli_si128(a, 16));
    T(_mm_packs_epi16(a, b)); T(_mm_packus_epi16(a, b)); T(_mm_packs_epi32(a, b)); T(_mm_packus_epi32(a, b));
    T(_mm_shuffle_epi32(a, 0x1b)); T(_mm_shufflelo_epi16(a, 0x8d)); T(_mm_shufflehi_epi16(a, 0x72));
    T(_mm_alignr_epi8(a, b, 5)); T(_mm_alignr_epi8(a, b, 20)); T(_mm_blendv_epi8(a, b, c)); T(_mm_blend_epi16(a, b, 0xa5));
    (void)c;
    return 0;
}

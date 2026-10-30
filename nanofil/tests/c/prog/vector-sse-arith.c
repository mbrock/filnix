// vectors
/* immintrin.h's SSE through SSE4.2 intrinsics, computed element by
   element (c_lower vector_op//6): multiplies, sums of absolute
   differences, averages, signs, pshufb, ptest, element extracts and
   inserts, sign masks, saturating and min/max elementwise builtins,
   compares, widening conversions, sets, horizontal adds, and cvtss2si
   and cvtsd2si rounding ties to even. Every result matches filcc's. */
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
    T(_mm_mul_epu32(a, b)); T(_mm_mul_epi32(a, b)); T(_mm_madd_epi16(a, b)); T(_mm_maddubs_epi16(a, b)); T(_mm_sad_epu8(a, b));
    T(_mm_mulhi_epu16(a, b)); T(_mm_mulhi_epi16(a, b)); T(_mm_mullo_epi16(a, b)); T(_mm_mullo_epi32(a, b));
    T(_mm_avg_epu8(a, b)); T(_mm_avg_epu16(a, b)); T(_mm_sign_epi8(a, b)); T(_mm_sign_epi16(a, b)); T(_mm_sign_epi32(a, b));
    T(_mm_shuffle_epi8(a, b));
    I(_mm_testz_si128(a, b)); I(_mm_testc_si128(a, b)); I(_mm_testnzc_si128(a, b)); I(_mm_testz_si128(a, _mm_setzero_si128()));
    I(_mm_extract_epi8(a, 3)); I(_mm_extract_epi16(a, 6)); I(_mm_extract_epi32(a, 2)); I(_mm_extract_epi64(a, 1) >> 7);
    T(_mm_insert_epi8(a, 0x55, 9)); T(_mm_insert_epi16(a, 0x1234, 3)); T(_mm_insert_epi32(a, -7, 1)); T(_mm_insert_epi64(a, 77, 0));
    I(_mm_movemask_epi8(a)); I(_mm_movemask_ps(_mm_castsi128_ps(a))); I(_mm_movemask_pd(_mm_castsi128_pd(a)));
    T(_mm_adds_epi8(a, b)); T(_mm_adds_epu8(a, b)); T(_mm_subs_epi16(a, b)); T(_mm_subs_epu16(a, b)); T(_mm_adds_epi16(a, b)); T(_mm_subs_epu8(a, b));
    T(_mm_min_epu8(a, b)); T(_mm_max_epi16(a, b)); T(_mm_min_epi8(a, b)); T(_mm_max_epu32(a, b)); T(_mm_min_epi32(a, b)); T(_mm_max_epu16(a, b));
    T(_mm_abs_epi8(a)); T(_mm_abs_epi16(a)); T(_mm_abs_epi32(a));
    T(_mm_unpacklo_epi8(a, b)); T(_mm_unpackhi_epi16(a, b)); T(_mm_unpacklo_epi32(a, b)); T(_mm_unpackhi_epi64(a, b));
    T(_mm_cmpeq_epi8(a, b)); T(_mm_cmpgt_epi16(a, b)); T(_mm_cmplt_epi32(a, b)); T(_mm_cmpgt_epi64(a, b)); T(_mm_cmpeq_epi64(a, a));
    T(_mm_add_epi8(a, b)); T(_mm_sub_epi16(a, b)); T(_mm_add_epi64(a, b)); T(_mm_and_si128(a, b)); T(_mm_andnot_si128(a, b)); T(_mm_or_si128(a, b)); T(_mm_xor_si128(a, b));
    T(_mm_cvtepu8_epi16(a)); T(_mm_cvtepi8_epi32(a)); T(_mm_cvtepi16_epi64(a)); T(_mm_cvtepu32_epi64(a));
    T(_mm_set_epi8(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16)); T(_mm_setr_epi16(1,-2,3,-4,5,-6,7,-8)); T(_mm_set_epi64x(-1, 5)); T(_mm_set1_epi16(-3));
    T(_mm_cvtsi64_si128(0x1122334455667788LL)); I(_mm_cvtsi128_si64(a) & 0xffff); T(_mm_loadl_epi64((const __m128i *)seed)); T(_mm_move_epi64(a));
    T(_mm_hadd_epi16(a, b)); T(_mm_hsub_epi32(a, b)); T(_mm_hadds_epi16(a, b));
    float fs[] = {1.5f, 2.5f, -0.5f, -1.5f, 3.4999f, 1e10f, -2.5f, 0.0f};
    for (int i = 0; i < 8; i++) I(_mm_cvt_ss2si(_mm_set_ss(fs[i])));
    double ds[] = {2.5, 3.5, -0.5, -7.5, 1e300, 4503599627370497.0};
    for (int i = 0; i < 6; i++) I(_mm_cvtsd_si32(_mm_set_sd(ds[i])));
    return 0;
}

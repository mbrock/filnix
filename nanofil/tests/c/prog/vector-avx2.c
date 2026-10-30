/* AVX2 on 32-byte vectors (part 1 of 9): each intrinsic on random and
   boundary inputs, hashed, against filcc, which runs the instructions
   natively. Per-lane builtins are the SSE ones on each 16-byte half;
   VPERMD, VPERM2I128, VINSERTI128/VEXTRACTI128, VPMOVMSKB and the
   element extracts cross lanes. Generated; vector-avx2.c through
   vector-avx2-9.c split the intrinsics for compile time. */
#include <immintrin.h>
#include <stdio.h>
#include <string.h>

#define AVX2 __attribute__((target("avx2,vpclmulqdq,pclmul")))
static unsigned long long st = 0x9e3779b97f4a7c15ull, hs = 1469598103934665603ull;
static unsigned rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return (unsigned)(st >> 11); }
static void mix(unsigned v) { hs = (hs ^ v) * 1099511628211ull; }
static const unsigned special[] = {0, 1, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000u, 0xffffffffu, 0x01010101u, 0x80808080u};
static void fill(unsigned *w, int n) {
    for (int i = 0; i < n; i++)
        w[i] = (rnd() & 3) ? (rnd() << 16 ^ rnd()) : special[rnd() % 13] ^ (rnd() & 1 ? 0 : (rnd() & 0x00ff00ffu));
}
AVX2 static void mixv(__m256i v) {
    unsigned w[8];
    _mm256_storeu_si256((__m256i *)w, v);
    for (int i = 0; i < 8; i++) mix(w[i]);
}
AVX2 static void one(int k, __m256i a, __m256i b, __m256i m, __m128i c, __m128i h) {
    switch (k) {
    case 0: mixv(_mm256_packs_epi16(a, b)); break; /* packs_epi16 */
    case 1: mixv(_mm256_mul_epu32(a, b)); break; /* mul_epu32 */
    case 2: mixv(_mm256_hadd_epi32(a, b)); break; /* hadd_epi32 */
    case 3: mixv(_mm256_add_epi64(a, b)); break; /* add_epi64 */
    case 4: mixv(_mm256_subs_epi8(a, b)); break; /* subs_epi8 */
    case 5: mixv(_mm256_cmpgt_epi16(a, b)); break; /* cmpgt_epi16 */
    case 6: mixv(_mm256_max_epi16(a, b)); break; /* max_epi16 */
    case 7: mixv(_mm256_unpackhi_epi16(a, b)); break; /* unpackhi_epi16 */
    case 8: mixv(_mm256_abs_epi32(a)); break; /* abs_epi32 */
    case 9: mixv(_mm256_slli_epi16(a, 15)); break; /* slli_epi16_15 */
    case 10: mixv(_mm256_srli_epi16(a, 7)); break; /* srli_epi16_7 */
    case 11: mixv(_mm256_srai_epi16(a, 1)); break; /* srai_epi16_1 */
    case 12: mixv(_mm256_slli_epi32(a, 0)); break; /* slli_epi32_0 */
    case 13: mixv(_mm256_slli_epi32(a, 200)); break; /* slli_epi32_200 */
    case 14: mixv(_mm256_srli_epi32(a, 64)); break; /* srli_epi32_64 */
    case 15: mixv(_mm256_srai_epi32(a, 63)); break; /* srai_epi32_63 */
    case 16: mixv(_mm256_slli_epi64(a, 33)); break; /* slli_epi64_33 */
    case 17: mixv(_mm256_srli_epi64(a, 31)); break; /* srli_epi64_31 */
    case 18: mixv(_mm256_srl_epi32(a, c)); break; /* srl_epi32 */
    case 19: mixv(_mm256_slli_si256(a, 20)); break; /* slli_si256_20 */
    case 20: mixv(_mm256_alignr_epi8(a, b, 8)); break; /* alignr_8 */
    case 21: mixv(_mm256_blend_epi16(a, b, 27)); break; /* blend_epi16_27 */
    case 22: mixv(_mm256_shufflehi_epi16(a, 78)); break; /* shufflehi_epi16_78 */
    case 23: mixv(_mm256_shufflelo_epi16(a, 255)); break; /* shufflelo_epi16_255 */
    case 24: mixv(_mm256_inserti128_si256(a, h, 0)); break; /* inserti128_0 */
    case 25: mixv(_mm256_zextsi128_si256(_mm256_extractf128_si256(a, 1))); break; /* extractf128_si256_1 */
    case 26: mixv(_mm256_permute2f128_si256(a, b, 49)); break; /* permute2f128_si256_49 */
    case 27: mixv(_mm256_permute2x128_si256(a, b, 136)); break; /* permute2x128_136 */
    case 28: mixv(_mm256_permute2f128_si256(a, b, 48)); break; /* permute2f128_si256_48 */
    case 29: mix((unsigned)(_mm256_movemask_epi8(a))); break; /* movemask_epi8 */
    case 30: mix((unsigned)(_mm256_movemask_ps(_mm256_castsi256_ps(a)))); break; /* movemask_ps */
    case 31: mix((unsigned)(_mm256_movemask_pd(_mm256_castsi256_pd(a)))); break; /* movemask_pd */
    case 32: mix((unsigned)(_mm256_cvtsi256_si32(a))); break; /* cvtsi256_si32 */
    case 33: mix((unsigned)(_mm256_extract_epi32(a, 0))); break; /* extract_epi32_0 */
    case 34: mix((unsigned)(_mm256_extract_epi32(a, 3))); break; /* extract_epi32_3 */
    case 35: mix((unsigned)(_mm256_extract_epi32(a, 7))); break; /* extract_epi32_7 */
    case 36: mix((unsigned)(_mm256_extract_epi8(a, 0))); break; /* extract_epi8_0 */
    case 37: mix((unsigned)(_mm256_extract_epi8(a, 17))); break; /* extract_epi8_17 */
    case 38: mix((unsigned)(_mm256_extract_epi8(a, 31))); break; /* extract_epi8_31 */
    case 39: mix((unsigned)(_mm256_extract_epi16(a, 0))); break; /* extract_epi16_0 */
    case 40: mix((unsigned)(_mm256_extract_epi16(a, 9))); break; /* extract_epi16_9 */
    case 41: mix((unsigned)(_mm256_extract_epi16(a, 15))); break; /* extract_epi16_15 */
    case 42: mix((unsigned)((int)(_mm256_extract_epi64(a, 0) >> 7))); break; /* extract_epi64_0 */
    case 43: mix((unsigned)((int)(_mm256_extract_epi64(a, 3) >> 7))); break; /* extract_epi64_3 */
    }
}

static const char *names[] = {"packs_epi16", "mul_epu32", "hadd_epi32", "add_epi64", "subs_epi8", "cmpgt_epi16", "max_epi16", "unpackhi_epi16", "abs_epi32", "slli_epi16_15", "srli_epi16_7", "srai_epi16_1", "slli_epi32_0", "slli_epi32_200", "srli_epi32_64", "srai_epi32_63", "slli_epi64_33", "srli_epi64_31", "srl_epi32", "slli_si256_20", "alignr_8", "blend_epi16_27", "shufflehi_epi16_78", "shufflelo_epi16_255", "inserti128_0", "extractf128_si256_1", "permute2f128_si256_49", "permute2x128_136", "permute2f128_si256_48", "movemask_epi8", "movemask_ps", "movemask_pd", "cvtsi256_si32", "extract_epi32_0", "extract_epi32_3", "extract_epi32_7", "extract_epi8_0", "extract_epi8_17", "extract_epi8_31", "extract_epi16_0", "extract_epi16_9", "extract_epi16_15", "extract_epi64_0", "extract_epi64_3"};
AVX2 static void run(void) {
    static const unsigned long long counts[] = {0, 1, 3, 7, 8, 15, 16, 31, 32, 63, 64, 65, 0x100000000ull, ~0ull};
    for (int k = 0; k < 44; k++) {
        hs = 1469598103934665603ull;
        for (int t = 0; t < 24; t++) {
            unsigned wa[8], wb[8], wm[8], wh[4];
            fill(wa, 8); fill(wb, 8); fill(wm, 8); fill(wh, 4);
            if (t == 0) memcpy(wb, wa, 32);
            __m256i a = _mm256_loadu_si256((const __m256i *)wa), b = _mm256_loadu_si256((const __m256i *)wb);
            __m256i m = _mm256_loadu_si256((const __m256i *)wm);
            __m128i h = _mm_loadu_si128((const __m128i *)wh);
            __m128i c = _mm_set_epi64x((long long)rnd() << 32 | rnd(), (long long)counts[t % 14]);
            one(k, a, b, m, c, h);
        }
        printf("%s %016llx\n", names[k], hs);
    }
}
int main(void) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx2") || !__builtin_cpu_supports("vpclmulqdq")) { puts("skip: no avx2"); return 0; }
    run();
    return 0;
}

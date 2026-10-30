/* AVX2 on 32-byte vectors (part 7 of 9): each intrinsic on random and
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
    case 0: mixv(_mm256_madd_epi16(a, b)); break; /* madd_epi16 */
    case 1: mixv(_mm256_sign_epi16(a, b)); break; /* sign_epi16 */
    case 2: mixv(_mm256_add_epi8(a, b)); break; /* add_epi8 */
    case 3: mixv(_mm256_adds_epi16(a, b)); break; /* adds_epi16 */
    case 4: mixv(_mm256_cmpeq_epi32(a, b)); break; /* cmpeq_epi32 */
    case 5: mixv(_mm256_andnot_si256(a, b)); break; /* andnot_si256 */
    case 6: mixv(_mm256_unpacklo_epi8(a, b)); break; /* unpacklo_epi8 */
    case 7: mixv(_mm256_castps_si256(_mm256_permutevar8x32_ps(_mm256_castsi256_ps(a), b))); break; /* permutevar8x32_ps */
    case 8: mixv(_mm256_slli_epi16(a, 0)); break; /* slli_epi16_0 */
    case 9: mixv(_mm256_slli_epi16(a, 200)); break; /* slli_epi16_200 */
    case 10: mixv(_mm256_srli_epi16(a, 64)); break; /* srli_epi16_64 */
    case 11: mixv(_mm256_srai_epi16(a, 63)); break; /* srai_epi16_63 */
    case 12: mixv(_mm256_slli_epi32(a, 33)); break; /* slli_epi32_33 */
    case 13: mixv(_mm256_srli_epi32(a, 31)); break; /* srli_epi32_31 */
    case 14: mixv(_mm256_srai_epi32(a, 16)); break; /* srai_epi32_16 */
    case 15: mixv(_mm256_slli_epi64(a, 15)); break; /* slli_epi64_15 */
    case 16: mixv(_mm256_srli_epi64(a, 7)); break; /* srli_epi64_7 */
    case 17: mixv(_mm256_srl_epi16(a, c)); break; /* srl_epi16 */
    case 18: mixv(_mm256_slli_si256(a, 5)); break; /* slli_si256_5 */
    case 19: mixv(_mm256_srli_si256(a, 20)); break; /* srli_si256_20 */
    case 20: mixv(_mm256_shuffle_epi32(a, 27)); break; /* shuffle_epi32_27 */
    case 21: mixv(_mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(a), _mm256_castsi256_ps(b), 228))); break; /* shuffle_ps_228 */
    case 22: mixv(_mm256_blend_epi16(a, b, 0)); break; /* blend_epi16_0 */
    case 23: mixv(_mm256_clmulepi64_epi128(a, b, 16)); break; /* clmul_16 */
    case 24: mixv(_mm256_zextsi128_si256(_mm_castpd_si128(_mm256_extractf128_pd(_mm256_castsi256_pd(a), 0)))); break; /* extractf128_pd_0 */
    case 25: mixv(_mm256_permute2x128_si256(a, b, 32)); break; /* permute2x128_32 */
    case 26: mixv(_mm256_permute2f128_si256(a, b, 8)); break; /* permute2f128_si256_8 */
    case 27: mixv(_mm256_permute2x128_si256(a, b, 33)); break; /* permute2x128_33 */
    case 28: mixv(_mm256_castpd_si256(_mm256_permute2f128_pd(_mm256_castsi256_pd(a), _mm256_castsi256_pd(b), 136))); break; /* permute2f128_pd_136 */
    }
}

static const char *names[] = {"madd_epi16", "sign_epi16", "add_epi8", "adds_epi16", "cmpeq_epi32", "andnot_si256", "unpacklo_epi8", "permutevar8x32_ps", "slli_epi16_0", "slli_epi16_200", "srli_epi16_64", "srai_epi16_63", "slli_epi32_33", "srli_epi32_31", "srai_epi32_16", "slli_epi64_15", "srli_epi64_7", "srl_epi16", "slli_si256_5", "srli_si256_20", "shuffle_epi32_27", "shuffle_ps_228", "blend_epi16_0", "clmul_16", "extractf128_pd_0", "permute2x128_32", "permute2f128_si256_8", "permute2x128_33", "permute2f128_pd_136"};
AVX2 static void run(void) {
    static const unsigned long long counts[] = {0, 1, 3, 7, 8, 15, 16, 31, 32, 63, 64, 65, 0x100000000ull, ~0ull};
    for (int k = 0; k < 29; k++) {
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

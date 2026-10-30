// vectors
/* AVX2 on 32-byte vectors (part 8 of 9): each intrinsic on random and
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
    case 0: mixv(_mm256_maddubs_epi16(a, b)); break; /* maddubs_epi16 */
    case 1: mixv(_mm256_sign_epi32(a, b)); break; /* sign_epi32 */
    case 2: mixv(_mm256_add_epi16(a, b)); break; /* add_epi16 */
    case 3: mixv(_mm256_adds_epu8(a, b)); break; /* adds_epu8 */
    case 4: mixv(_mm256_cmpeq_epi64(a, b)); break; /* cmpeq_epi64 */
    case 5: mixv(_mm256_min_epi8(a, b)); break; /* min_epi8 */
    case 6: mixv(_mm256_unpackhi_epi8(a, b)); break; /* unpackhi_epi8 */
    case 7: mixv(_mm256_abs_epi8(a)); break; /* abs_epi8 */
    case 8: mixv(_mm256_slli_epi16(a, 1)); break; /* slli_epi16_1 */
    case 9: mixv(_mm256_srli_epi16(a, 0)); break; /* srli_epi16_0 */
    case 10: mixv(_mm256_srli_epi16(a, 200)); break; /* srli_epi16_200 */
    case 11: mixv(_mm256_srai_epi16(a, 64)); break; /* srai_epi16_64 */
    case 12: mixv(_mm256_slli_epi32(a, 63)); break; /* slli_epi32_63 */
    case 13: mixv(_mm256_srli_epi32(a, 33)); break; /* srli_epi32_33 */
    case 14: mixv(_mm256_srai_epi32(a, 31)); break; /* srai_epi32_31 */
    case 15: mixv(_mm256_slli_epi64(a, 16)); break; /* slli_epi64_16 */
    case 16: mixv(_mm256_srli_epi64(a, 15)); break; /* srli_epi64_15 */
    case 17: mixv(_mm256_sra_epi16(a, c)); break; /* sra_epi16 */
    case 18: mixv(_mm256_slli_si256(a, 15)); break; /* slli_si256_15 */
    case 19: mixv(_mm256_alignr_epi8(a, b, 0)); break; /* alignr_0 */
    case 20: mixv(_mm256_shufflelo_epi16(a, 27)); break; /* shufflelo_epi16_27 */
    case 21: mixv(_mm256_shuffle_epi32(a, 78)); break; /* shuffle_epi32_78 */
    case 22: mixv(_mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(a), _mm256_castsi256_ps(b), 0))); break; /* shuffle_ps_0 */
    case 23: mixv(_mm256_clmulepi64_epi128(a, b, 17)); break; /* clmul_17 */
    case 24: mixv(_mm256_zextsi128_si256(_mm256_extracti128_si256(a, 1))); break; /* extracti128_1 */
    case 25: mixv(_mm256_permute2f128_si256(a, b, 32)); break; /* permute2f128_si256_32 */
    case 26: mixv(_mm256_permute2x128_si256(a, b, 128)); break; /* permute2x128_128 */
    case 27: mixv(_mm256_permute2f128_si256(a, b, 33)); break; /* permute2f128_si256_33 */
    }
}

static const char *names[] = {"maddubs_epi16", "sign_epi32", "add_epi16", "adds_epu8", "cmpeq_epi64", "min_epi8", "unpackhi_epi8", "abs_epi8", "slli_epi16_1", "srli_epi16_0", "srli_epi16_200", "srai_epi16_64", "slli_epi32_63", "srli_epi32_33", "srai_epi32_31", "slli_epi64_16", "srli_epi64_15", "sra_epi16", "slli_si256_15", "alignr_0", "shufflelo_epi16_27", "shuffle_epi32_78", "shuffle_ps_0", "clmul_17", "extracti128_1", "permute2f128_si256_32", "permute2x128_128", "permute2f128_si256_33"};
AVX2 static void run(void) {
    static const unsigned long long counts[] = {0, 1, 3, 7, 8, 15, 16, 31, 32, 63, 64, 65, 0x100000000ull, ~0ull};
    for (int k = 0; k < 28; k++) {
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

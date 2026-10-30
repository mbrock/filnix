/* AVX2 on 32-byte vectors (part 2 of 9): each intrinsic on random and
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
    case 0: mixv(_mm256_packs_epi32(a, b)); break; /* packs_epi32 */
    case 1: mixv(_mm256_mulhi_epi16(a, b)); break; /* mulhi_epi16 */
    case 2: mixv(_mm256_hadds_epi16(a, b)); break; /* hadds_epi16 */
    case 3: mixv(_mm256_sub_epi8(a, b)); break; /* sub_epi8 */
    case 4: mixv(_mm256_subs_epi16(a, b)); break; /* subs_epi16 */
    case 5: mixv(_mm256_cmpgt_epi32(a, b)); break; /* cmpgt_epi32 */
    case 6: mixv(_mm256_max_epu16(a, b)); break; /* max_epu16 */
    case 7: mixv(_mm256_unpacklo_epi32(a, b)); break; /* unpacklo_epi32 */
    case 8: mixv(_mm256_cvtepu8_epi16(h)); break; /* cvtepu8_epi16 */
    case 9: mixv(_mm256_slli_epi16(a, 16)); break; /* slli_epi16_16 */
    case 10: mixv(_mm256_srli_epi16(a, 15)); break; /* srli_epi16_15 */
    case 11: mixv(_mm256_srai_epi16(a, 7)); break; /* srai_epi16_7 */
    case 12: mixv(_mm256_slli_epi32(a, 1)); break; /* slli_epi32_1 */
    case 13: mixv(_mm256_srli_epi32(a, 0)); break; /* srli_epi32_0 */
    case 14: mixv(_mm256_srli_epi32(a, 200)); break; /* srli_epi32_200 */
    case 15: mixv(_mm256_srai_epi32(a, 64)); break; /* srai_epi32_64 */
    case 16: mixv(_mm256_slli_epi64(a, 63)); break; /* slli_epi64_63 */
    case 17: mixv(_mm256_srli_epi64(a, 33)); break; /* srli_epi64_33 */
    case 18: mixv(_mm256_sra_epi32(a, c)); break; /* sra_epi32 */
    case 19: mixv(_mm256_srli_si256(a, 0)); break; /* srli_si256_0 */
    case 20: mixv(_mm256_alignr_epi8(a, b, 15)); break; /* alignr_15 */
    case 21: mixv(_mm256_castps_si256(_mm256_shuffle_ps(_mm256_castsi256_ps(a), _mm256_castsi256_ps(b), 27))); break; /* shuffle_ps_27 */
    case 22: mixv(_mm256_blend_epi16(a, b, 78)); break; /* blend_epi16_78 */
    case 23: mixv(_mm256_shufflehi_epi16(a, 255)); break; /* shufflehi_epi16_255 */
    case 24: mixv(_mm256_zextsi128_si256(_mm256_extractf128_si256(a, 0))); break; /* extractf128_si256_0 */
    case 25: mixv(_mm256_insertf128_si256(a, h, 1)); break; /* insertf128_si256_1 */
    case 26: mixv(_mm256_permute2x128_si256(a, b, 2)); break; /* permute2x128_2 */
    case 27: mixv(_mm256_permute2f128_si256(a, b, 136)); break; /* permute2f128_si256_136 */
    case 28: mixv(_mm256_castps_si256(_mm256_permute2f128_ps(_mm256_castsi256_ps(a), _mm256_castsi256_ps(b), 32))); break; /* permute2f128_ps_32 */
    }
}

static const char *names[] = {"packs_epi32", "mulhi_epi16", "hadds_epi16", "sub_epi8", "subs_epi16", "cmpgt_epi32", "max_epu16", "unpacklo_epi32", "cvtepu8_epi16", "slli_epi16_16", "srli_epi16_15", "srai_epi16_7", "slli_epi32_1", "srli_epi32_0", "srli_epi32_200", "srai_epi32_64", "slli_epi64_63", "srli_epi64_33", "sra_epi32", "srli_si256_0", "alignr_15", "shuffle_ps_27", "blend_epi16_78", "shufflehi_epi16_255", "extractf128_si256_0", "insertf128_si256_1", "permute2x128_2", "permute2f128_si256_136", "permute2f128_ps_32"};
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

// vectors
/* AVX, FMA and SSE3 floating-point builtins (fftw's simd-avx*.h) (part 2 of 2):
   each on random finite, infinite, zero and subnormal inputs, hashed
   bit for bit against filcc, which runs them natively. FMA rounds once
   (libm's fma); NaN inputs are left out, since which NaN an FMA returns
   depends on the operand order clang picks. Generated; vector-avx-float.c and vector-avx-float-2.c split the
   builtins for compile time. */
#include <immintrin.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

#define AVX __attribute__((target("avx2,fma")))
static unsigned long long st = 0x2545f4914f6cdd1dull, hs = 1469598103934665603ull;
static unsigned rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return (unsigned)(st >> 11); }
static void mix(unsigned v) { hs = (hs ^ v) * 1099511628211ull; }
static const double special[] = {0.0, -0.0, 1.0, -1.0, 0.5, 3.0, 1e308, -1e308, 1e-310, -4.9e-324, INFINITY, -INFINITY, 1e38, 3e-39, 0.1, 2.5e-8};
static void fill(unsigned *w, int dbl) {
    for (int i = 0; i < 8; i += dbl ? 2 : 1) {
        if (rnd() % 3 == 0) {
            double d = special[rnd() % 16];
            if (dbl) memcpy(w + i, &d, 8); else { float f = (float)d; memcpy(w + i, &f, 4); }
        } else if (dbl) {
            double d = ldexp((double)(rnd() % 2000000) - 1000000.0, (int)(rnd() % 80) - 40);
            memcpy(w + i, &d, 8);
        } else {
            float f = ldexpf((float)(rnd() % 20000) - 10000.0f, (int)(rnd() % 40) - 20);
            memcpy(w + i, &f, 4);
        }
    }
}
#define Lps(w) _mm_loadu_ps((const float *)(w))
#define Lpd(w) _mm_loadu_pd((const double *)(w))
#define L256ps(w) _mm256_loadu_ps((const float *)(w))
#define L256pd(w) _mm256_loadu_pd((const double *)(w))
AVX static void Sps(__m128 v) { unsigned o[4]; _mm_storeu_ps((float *)o, v); for (int i = 0; i < 4; i++) mix(o[i]); }
AVX static void Spd(__m128d v) { unsigned o[4]; _mm_storeu_pd((double *)o, v); for (int i = 0; i < 4; i++) mix(o[i]); }
AVX static void S256ps(__m256 v) { unsigned o[8]; _mm256_storeu_ps((float *)o, v); for (int i = 0; i < 8; i++) mix(o[i]); }
AVX static void S256pd(__m256d v) { unsigned o[8]; _mm256_storeu_pd((double *)o, v); for (int i = 0; i < 8; i++) mix(o[i]); }
AVX static void one(int k, const unsigned *wa, const unsigned *wb, const unsigned *wc) {
    switch (k) {
    case 0: Sps(_mm_add_ps(Lps(wa), Lps(wb))); break; /* add_ps */
    case 1: Sps(_mm_mul_ps(Lps(wa), Lps(wb))); break; /* mul_ps */
    case 2: Sps(_mm_xor_ps(Lps(wa), Lps(wb))); break; /* xor_ps */
    case 3: Sps(_mm_unpackhi_ps(Lps(wa), Lps(wb))); break; /* unpackhi_ps */
    case 4: Sps(_mm_fmsub_ps(Lps(wa), Lps(wb), Lps(wc))); break; /* fmsub_ps */
    case 5: Sps(_mm_fnmsub_ps(Lps(wa), Lps(wb), Lps(wc))); break; /* fnmsub_ps */
    case 6: Sps(_mm_fmsubadd_ps(Lps(wa), Lps(wb), Lps(wc))); break; /* fmsubadd_ps */
    case 7: Sps(_mm_permute_ps(Lps(wa), 228)); break; /* permute_ps_228 */
    case 8: Sps(_mm_permute_ps(Lps(wa), 177)); break; /* permute_ps_177 */
    case 9: Sps(_mm_permute_ps(Lps(wa), 255)); break; /* permute_ps_255 */
    case 10: Spd(_mm_add_pd(Lpd(wa), Lpd(wb))); break; /* add_pd */
    case 11: Spd(_mm_mul_pd(Lpd(wa), Lpd(wb))); break; /* mul_pd */
    case 12: Spd(_mm_xor_pd(Lpd(wa), Lpd(wb))); break; /* xor_pd */
    case 13: Spd(_mm_unpackhi_pd(Lpd(wa), Lpd(wb))); break; /* unpackhi_pd */
    case 14: Spd(_mm_fmsub_pd(Lpd(wa), Lpd(wb), Lpd(wc))); break; /* fmsub_pd */
    case 15: Spd(_mm_fnmsub_pd(Lpd(wa), Lpd(wb), Lpd(wc))); break; /* fnmsub_pd */
    case 16: Spd(_mm_fmsubadd_pd(Lpd(wa), Lpd(wb), Lpd(wc))); break; /* fmsubadd_pd */
    case 17: Spd(_mm_permute_pd(Lpd(wa), 1)); break; /* permute_pd_1 */
    case 18: Spd(_mm_permute_pd(Lpd(wa), 3)); break; /* permute_pd_3 */
    case 19: S256ps(_mm256_add_ps(L256ps(wa), L256ps(wb))); break; /* add256_ps */
    case 20: S256ps(_mm256_mul_ps(L256ps(wa), L256ps(wb))); break; /* mul256_ps */
    case 21: S256ps(_mm256_xor_ps(L256ps(wa), L256ps(wb))); break; /* xor256_ps */
    case 22: S256ps(_mm256_unpackhi_ps(L256ps(wa), L256ps(wb))); break; /* unpackhi256_ps */
    case 23: S256ps(_mm256_fmsub_ps(L256ps(wa), L256ps(wb), L256ps(wc))); break; /* fmsub256_ps */
    case 24: S256ps(_mm256_fnmsub_ps(L256ps(wa), L256ps(wb), L256ps(wc))); break; /* fnmsub256_ps */
    case 25: S256ps(_mm256_fmsubadd_ps(L256ps(wa), L256ps(wb), L256ps(wc))); break; /* fmsubadd256_ps */
    case 26: S256ps(_mm256_permute_ps(L256ps(wa), 228)); break; /* permute256_ps_228 */
    case 27: S256ps(_mm256_permute_ps(L256ps(wa), 177)); break; /* permute256_ps_177 */
    case 28: S256ps(_mm256_permute_ps(L256ps(wa), 255)); break; /* permute256_ps_255 */
    case 29: S256ps(_mm256_shuffle_ps(L256ps(wa), L256ps(wb), 228)); break; /* shuffle256_ps_228 */
    case 30: S256ps(_mm256_shuffle_ps(L256ps(wa), L256ps(wb), 177)); break; /* shuffle256_ps_177 */
    case 31: S256pd(_mm256_add_pd(L256pd(wa), L256pd(wb))); break; /* add256_pd */
    case 32: S256pd(_mm256_mul_pd(L256pd(wa), L256pd(wb))); break; /* mul256_pd */
    case 33: S256pd(_mm256_xor_pd(L256pd(wa), L256pd(wb))); break; /* xor256_pd */
    case 34: S256pd(_mm256_unpackhi_pd(L256pd(wa), L256pd(wb))); break; /* unpackhi256_pd */
    case 35: S256pd(_mm256_fmsub_pd(L256pd(wa), L256pd(wb), L256pd(wc))); break; /* fmsub256_pd */
    case 36: S256pd(_mm256_fnmsub_pd(L256pd(wa), L256pd(wb), L256pd(wc))); break; /* fnmsub256_pd */
    case 37: S256pd(_mm256_fmsubadd_pd(L256pd(wa), L256pd(wb), L256pd(wc))); break; /* fmsubadd256_pd */
    case 38: S256pd(_mm256_permute_pd(L256pd(wa), 5)); break; /* permute256_pd_5 */
    case 39: S256pd(_mm256_permute_pd(L256pd(wa), 15)); break; /* permute256_pd_15 */
    case 40: S256pd(_mm256_permute_pd(L256pd(wa), 9)); break; /* permute256_pd_9 */
    case 41: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 5)); break; /* shuffle256_pd_5 */
    case 42: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 15)); break; /* shuffle256_pd_15 */
    case 43: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 9)); break; /* shuffle256_pd_9 */
    case 44: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 12)); break; /* shuffle256_pd_12 */
    case 45: S256ps(_mm256_moveldup_ps(L256ps(wa))); break; /* moveldup256 */
    case 46: Sps(_mm_movehdup_ps(Lps(wa))); break; /* movehdup */
    }
}
static const char *names[] = {"add_ps", "mul_ps", "xor_ps", "unpackhi_ps", "fmsub_ps", "fnmsub_ps", "fmsubadd_ps", "permute_ps_228", "permute_ps_177", "permute_ps_255", "add_pd", "mul_pd", "xor_pd", "unpackhi_pd", "fmsub_pd", "fnmsub_pd", "fmsubadd_pd", "permute_pd_1", "permute_pd_3", "add256_ps", "mul256_ps", "xor256_ps", "unpackhi256_ps", "fmsub256_ps", "fnmsub256_ps", "fmsubadd256_ps", "permute256_ps_228", "permute256_ps_177", "permute256_ps_255", "shuffle256_ps_228", "shuffle256_ps_177", "add256_pd", "mul256_pd", "xor256_pd", "unpackhi256_pd", "fmsub256_pd", "fnmsub256_pd", "fmsubadd256_pd", "permute256_pd_5", "permute256_pd_15", "permute256_pd_9", "shuffle256_pd_5", "shuffle256_pd_15", "shuffle256_pd_9", "shuffle256_pd_12", "moveldup256", "movehdup"};
static const int dbl[] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0};
int main(void) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx2") || !__builtin_cpu_supports("fma")) { puts("skip: no avx2 or fma"); return 0; }
    for (int k = 0; k < 47; k++) {
        hs = 1469598103934665603ull;
        for (int t = 0; t < 24; t++) {
            unsigned wa[8], wb[8], wc[8];
            fill(wa, dbl[k]); fill(wb, dbl[k]); fill(wc, dbl[k]);
            one(k, wa, wb, wc);
        }
        printf("%s %016llx\n", names[k], hs);
    }
    return 0;
}

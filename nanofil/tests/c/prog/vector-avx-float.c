/* AVX, FMA and SSE3 floating-point builtins (fftw's simd-avx*.h) (part 1 of 2):
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
    case 0: Sps(_mm_addsub_ps(Lps(wa), Lps(wb))); break; /* addsub_ps */
    case 1: Sps(_mm_sub_ps(Lps(wa), Lps(wb))); break; /* sub_ps */
    case 2: Sps(_mm_div_ps(Lps(wa), Lps(wb))); break; /* div_ps */
    case 3: Sps(_mm_unpacklo_ps(Lps(wa), Lps(wb))); break; /* unpacklo_ps */
    case 4: Sps(_mm_fmadd_ps(Lps(wa), Lps(wb), Lps(wc))); break; /* fmadd_ps */
    case 5: Sps(_mm_fnmadd_ps(Lps(wa), Lps(wb), Lps(wc))); break; /* fnmadd_ps */
    case 6: Sps(_mm_fmaddsub_ps(Lps(wa), Lps(wb), Lps(wc))); break; /* fmaddsub_ps */
    case 7: Sps(_mm_permute_ps(Lps(wa), 27)); break; /* permute_ps_27 */
    case 8: Sps(_mm_permute_ps(Lps(wa), 78)); break; /* permute_ps_78 */
    case 9: Sps(_mm_permute_ps(Lps(wa), 0)); break; /* permute_ps_0 */
    case 10: Spd(_mm_addsub_pd(Lpd(wa), Lpd(wb))); break; /* addsub_pd */
    case 11: Spd(_mm_sub_pd(Lpd(wa), Lpd(wb))); break; /* sub_pd */
    case 12: Spd(_mm_div_pd(Lpd(wa), Lpd(wb))); break; /* div_pd */
    case 13: Spd(_mm_unpacklo_pd(Lpd(wa), Lpd(wb))); break; /* unpacklo_pd */
    case 14: Spd(_mm_fmadd_pd(Lpd(wa), Lpd(wb), Lpd(wc))); break; /* fmadd_pd */
    case 15: Spd(_mm_fnmadd_pd(Lpd(wa), Lpd(wb), Lpd(wc))); break; /* fnmadd_pd */
    case 16: Spd(_mm_fmaddsub_pd(Lpd(wa), Lpd(wb), Lpd(wc))); break; /* fmaddsub_pd */
    case 17: Spd(_mm_permute_pd(Lpd(wa), 0)); break; /* permute_pd_0 */
    case 18: Spd(_mm_permute_pd(Lpd(wa), 2)); break; /* permute_pd_2 */
    case 19: S256ps(_mm256_addsub_ps(L256ps(wa), L256ps(wb))); break; /* addsub256_ps */
    case 20: S256ps(_mm256_sub_ps(L256ps(wa), L256ps(wb))); break; /* sub256_ps */
    case 21: S256ps(_mm256_div_ps(L256ps(wa), L256ps(wb))); break; /* div256_ps */
    case 22: S256ps(_mm256_unpacklo_ps(L256ps(wa), L256ps(wb))); break; /* unpacklo256_ps */
    case 23: S256ps(_mm256_fmadd_ps(L256ps(wa), L256ps(wb), L256ps(wc))); break; /* fmadd256_ps */
    case 24: S256ps(_mm256_fnmadd_ps(L256ps(wa), L256ps(wb), L256ps(wc))); break; /* fnmadd256_ps */
    case 25: S256ps(_mm256_fmaddsub_ps(L256ps(wa), L256ps(wb), L256ps(wc))); break; /* fmaddsub256_ps */
    case 26: S256ps(_mm256_permute_ps(L256ps(wa), 27)); break; /* permute256_ps_27 */
    case 27: S256ps(_mm256_permute_ps(L256ps(wa), 78)); break; /* permute256_ps_78 */
    case 28: S256ps(_mm256_permute_ps(L256ps(wa), 0)); break; /* permute256_ps_0 */
    case 29: S256ps(_mm256_shuffle_ps(L256ps(wa), L256ps(wb), 27)); break; /* shuffle256_ps_27 */
    case 30: S256ps(_mm256_shuffle_ps(L256ps(wa), L256ps(wb), 78)); break; /* shuffle256_ps_78 */
    case 31: S256pd(_mm256_addsub_pd(L256pd(wa), L256pd(wb))); break; /* addsub256_pd */
    case 32: S256pd(_mm256_sub_pd(L256pd(wa), L256pd(wb))); break; /* sub256_pd */
    case 33: S256pd(_mm256_div_pd(L256pd(wa), L256pd(wb))); break; /* div256_pd */
    case 34: S256pd(_mm256_unpacklo_pd(L256pd(wa), L256pd(wb))); break; /* unpacklo256_pd */
    case 35: S256pd(_mm256_fmadd_pd(L256pd(wa), L256pd(wb), L256pd(wc))); break; /* fmadd256_pd */
    case 36: S256pd(_mm256_fnmadd_pd(L256pd(wa), L256pd(wb), L256pd(wc))); break; /* fnmadd256_pd */
    case 37: S256pd(_mm256_fmaddsub_pd(L256pd(wa), L256pd(wb), L256pd(wc))); break; /* fmaddsub256_pd */
    case 38: S256pd(_mm256_permute_pd(L256pd(wa), 0)); break; /* permute256_pd_0 */
    case 39: S256pd(_mm256_permute_pd(L256pd(wa), 10)); break; /* permute256_pd_10 */
    case 40: S256pd(_mm256_permute_pd(L256pd(wa), 6)); break; /* permute256_pd_6 */
    case 41: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 0)); break; /* shuffle256_pd_0 */
    case 42: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 10)); break; /* shuffle256_pd_10 */
    case 43: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 6)); break; /* shuffle256_pd_6 */
    case 44: S256pd(_mm256_shuffle_pd(L256pd(wa), L256pd(wb), 3)); break; /* shuffle256_pd_3 */
    case 45: S256ps(_mm256_movehdup_ps(L256ps(wa))); break; /* movehdup256 */
    case 46: S256pd(_mm256_movedup_pd(L256pd(wa))); break; /* movedup256 */
    case 47: Sps(_mm_moveldup_ps(Lps(wa))); break; /* moveldup */
    }
}
static const char *names[] = {"addsub_ps", "sub_ps", "div_ps", "unpacklo_ps", "fmadd_ps", "fnmadd_ps", "fmaddsub_ps", "permute_ps_27", "permute_ps_78", "permute_ps_0", "addsub_pd", "sub_pd", "div_pd", "unpacklo_pd", "fmadd_pd", "fnmadd_pd", "fmaddsub_pd", "permute_pd_0", "permute_pd_2", "addsub256_ps", "sub256_ps", "div256_ps", "unpacklo256_ps", "fmadd256_ps", "fnmadd256_ps", "fmaddsub256_ps", "permute256_ps_27", "permute256_ps_78", "permute256_ps_0", "shuffle256_ps_27", "shuffle256_ps_78", "addsub256_pd", "sub256_pd", "div256_pd", "unpacklo256_pd", "fmadd256_pd", "fnmadd256_pd", "fmaddsub256_pd", "permute256_pd_0", "permute256_pd_10", "permute256_pd_6", "shuffle256_pd_0", "shuffle256_pd_10", "shuffle256_pd_6", "shuffle256_pd_3", "movehdup256", "movedup256", "moveldup"};
static const int dbl[] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0};
int main(void) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx2") || !__builtin_cpu_supports("fma")) { puts("skip: no avx2 or fma"); return 0; }
    for (int k = 0; k < 48; k++) {
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

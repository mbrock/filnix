/* PCLMULQDQ (_mm_clmulepi64_si128): the carry-less product of the
   quadwords imm8 bits 0 and 4 select, as xz's, libdeflate's and tor's
   CRC and POLYVAL code uses it, in a function with the pclmul target. */
#include <immintrin.h>
#include <stdio.h>

static unsigned long long st = 0x9e3779b97f4a7c15ull;
static unsigned long long rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }

__attribute__((target("pclmul,sse4.1")))
static __m128i mul(__m128i a, __m128i b, int k) {
    switch (k) {
    case 0: return _mm_clmulepi64_si128(a, b, 0x00);
    case 1: return _mm_clmulepi64_si128(a, b, 0x01);
    case 2: return _mm_clmulepi64_si128(a, b, 0x10);
    case 3: return _mm_clmulepi64_si128(a, b, 0x11);
    default: return _mm_clmulepi64_si128(a, b, 0xee);   /* only bits 0 and 4 count */
    }
}

int main(void) {
    unsigned long long edge[] = {0, 1, 2, 0x8000000000000000ull, ~0ull, 0x5555555555555555ull};
    unsigned long long h = 0;
    for (int i = 0; i < 6; i++)
        for (int j = 0; j < 6; j++) {
            __m128i a = _mm_set_epi64x(edge[j], edge[i]), b = _mm_set_epi64x(edge[i], edge[j]);
            for (int k = 0; k < 5; k++) {
                __m128i r = mul(a, b, k);
                unsigned long long lo = _mm_cvtsi128_si64(r), hi = _mm_extract_epi64(r, 1);
                if (i == 4 && j == 4) printf("%d %016llx %016llx\n", k, hi, lo);
                h = h * 31 + lo; h = h * 31 + hi;
            }
        }
    for (int n = 0; n < 2000; n++) {
        __m128i a = _mm_set_epi64x(rnd(), rnd()), b = _mm_set_epi64x(rnd(), rnd());
        __m128i r = mul(a, b, n % 5);
        h = h * 31 + _mm_cvtsi128_si64(r); h = h * 31 + _mm_extract_epi64(r, 1);
    }
    printf("%016llx\n", h);
    return 0;
}

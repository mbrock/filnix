// vectors
/* SSE4.2's explicit-length string compare on bytes returning a mask
   (_mm_cmpestrm), which filcc compiles natively, on data from small
   alphabets (so elements match, and periodic strings so long runs of
   them match) with lengths negative, zero, saturating, INT_MIN and
   INT_MAX, and zeros inside for the implicit lengths. vector-sse42.c,
   vector-sse42-mask.c and vector-sse42-words.c cover each of the 64
   element formats, aggregations and polarities, with both index ends and
   mask forms, between them; vector-sse42-forms.c samples the implicit-
   length forms and the flags. */
#include <immintrin.h>
#include <limits.h>
#include <stdio.h>

static unsigned long long st = 0x2545f4914f6cdd1dull, h = 1469598103934665603ull;
static unsigned rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return (unsigned)(st >> 11); }
static int verbose;
static void mix(const char *n, int k, unsigned v) {
    h = (h ^ v ^ ((unsigned long long)k << 40)) * 1099511628211ull;
    if (verbose) printf("%s %d %u\n", n, k, v);
}
static void mixv(const char *n, int k, __m128i v) {
    unsigned long long lo = (unsigned long long)_mm_cvtsi128_si64(v), hi = (unsigned long long)_mm_extract_epi64(v, 1);
    mix(n, k, (unsigned)lo); mix(n, k, (unsigned)(lo >> 32)); mix(n, k, (unsigned)hi); mix(n, k, (unsigned)(hi >> 32));
}
__attribute__((target("sse4.2"))) static __m128i estrm_0(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestrm(a, la, b, lb, 68);
    case 1: return _mm_cmpestrm(a, la, b, lb, 70);
    case 2: return _mm_cmpestrm(a, la, b, lb, 76);
    case 3: return _mm_cmpestrm(a, la, b, lb, 78);
    case 4: return _mm_cmpestrm(a, la, b, lb, 20);
    case 5: return _mm_cmpestrm(a, la, b, lb, 22);
    case 6: return _mm_cmpestrm(a, la, b, lb, 28);
    case 7: return _mm_cmpestrm(a, la, b, lb, 30);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static __m128i estrm_1(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestrm(a, la, b, lb, 100);
    case 1: return _mm_cmpestrm(a, la, b, lb, 102);
    case 2: return _mm_cmpestrm(a, la, b, lb, 108);
    case 3: return _mm_cmpestrm(a, la, b, lb, 110);
    case 4: return _mm_cmpestrm(a, la, b, lb, 52);
    case 5: return _mm_cmpestrm(a, la, b, lb, 54);
    case 6: return _mm_cmpestrm(a, la, b, lb, 60);
    case 7: return _mm_cmpestrm(a, la, b, lb, 62);
    }
    __builtin_unreachable();
}

static __m128i data(int kind) {
    static const unsigned char alpha[] = {'a', 'b', 'c', 0, 0xff, 0x80, 0x7f, 1};
    unsigned char x[16];
    for (int i = 0; i < 16; i++) {
        unsigned r = rnd();
        x[i] = kind == 0 ? alpha[r % 8] : kind == 1 ? (unsigned char)r
             : kind == 2 ? alpha[r % 3] : alpha[i % 2];
        if (kind == 2 && r % 11 == 0) x[i] = 0;
    }
    if (kind == 3) x[8 + rnd() % 8] = 'c';         /* periodic, one late flip: long partial matches */
    return _mm_loadu_si128((const __m128i *)x);
}

int main(void) {
    static const int lens[] = {-20, -16, -9, -8, -1, 0, 1, 3, 7, 8, 9, 15, 16, 17, 100, INT_MIN, INT_MAX};
    for (int t = 0; t < 60; t++) {
        verbose = t == 0;
        __m128i a = data(t % 4), b = data(t % 8 < 4 ? (t + 1) % 4 : 3);
        int la = lens[rnd() % 17], lb = lens[rnd() % 17];
        if (t == 1) b = a, la = lb = 16;           /* equal strings */
        for (int k = 0; k < 8; k++) mixv("estrm_0", k, estrm_0(a, la, b, lb, k));
        for (int k = 0; k < 8; k++) mixv("estrm_1", k, estrm_1(a, la, b, lb, k));
    }
    printf("%016llx\n", h);
    return 0;
}

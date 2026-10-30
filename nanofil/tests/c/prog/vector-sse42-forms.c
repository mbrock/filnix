// vectors
/* SSE4.2's implicit-length string compares (_mm_cmpistri, _mm_cmpistrm)
   and the flag forms (_mm_cmp[ei]str[acosz]), which filcc compiles
   natively, on data from small alphabets (so elements match, and
   periodic strings so long runs of them match) with lengths negative,
   zero, saturating, INT_MIN and INT_MAX, and zeros inside for the
   implicit lengths. vector-sse42.c, vector-sse42-mask.c and vector-
   sse42-words.c cover each of the 64 element formats, aggregations and
   polarities, with both index ends and mask forms, between them; vector-
   sse42-forms.c samples the implicit-length forms and the flags. */
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
__attribute__((target("sse4.2"))) static int istri(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistri(a, b, 13);
    case 1: return _mm_cmpistri(a, b, 43);
    case 2: return _mm_cmpistri(a, b, 68);
    case 3: return _mm_cmpistri(a, b, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static __m128i istrm(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistrm(a, b, 13);
    case 1: return _mm_cmpistrm(a, b, 43);
    case 2: return _mm_cmpistrm(a, b, 68);
    case 3: return _mm_cmpistrm(a, b, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int estra(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestra(a, la, b, lb, 13);
    case 1: return _mm_cmpestra(a, la, b, lb, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int istra(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistra(a, b, 13);
    case 1: return _mm_cmpistra(a, b, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int estrc(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestrc(a, la, b, lb, 13);
    case 1: return _mm_cmpestrc(a, la, b, lb, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int istrc(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistrc(a, b, 13);
    case 1: return _mm_cmpistrc(a, b, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int estro(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestro(a, la, b, lb, 13);
    case 1: return _mm_cmpestro(a, la, b, lb, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int istro(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistro(a, b, 13);
    case 1: return _mm_cmpistro(a, b, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int estrs(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestrs(a, la, b, lb, 13);
    case 1: return _mm_cmpestrs(a, la, b, lb, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int istrs(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistrs(a, b, 13);
    case 1: return _mm_cmpistrs(a, b, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int estrz(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpestrz(a, la, b, lb, 13);
    case 1: return _mm_cmpestrz(a, la, b, lb, 122);
    }
    __builtin_unreachable();
}

__attribute__((target("sse4.2"))) static int istrz(__m128i a, int la, __m128i b, int lb, int k) {
    switch (k) {
    case 0: return _mm_cmpistrz(a, b, 13);
    case 1: return _mm_cmpistrz(a, b, 122);
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
        for (int k = 0; k < 4; k++) mix("istri", k, (unsigned)istri(a, la, b, lb, k));
        for (int k = 0; k < 4; k++) mixv("istrm", k, istrm(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("estra", k, (unsigned)estra(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("istra", k, (unsigned)istra(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("estrc", k, (unsigned)estrc(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("istrc", k, (unsigned)istrc(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("estro", k, (unsigned)estro(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("istro", k, (unsigned)istro(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("estrs", k, (unsigned)estrs(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("istrs", k, (unsigned)istrs(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("estrz", k, (unsigned)estrz(a, la, b, lb, k));
        for (int k = 0; k < 2; k++) mix("istrz", k, (unsigned)istrz(a, la, b, lb, k));
    }
    printf("%016llx\n", h);
    return 0;
}

/* Link against each rebuilt libcrypto.a, not the extracted assembly fixture.
   bench times the port's C add/sub and two real Montgomery assembly paths.
   check FLAGS poisons only the secret operands using ct-memcmp/zeg.s. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdfil.h>

typedef unsigned long word;
word bn_add_words(word *, const word *, const word *, int);
word bn_sub_words(word *, const word *, const word *, int);
int bn_mul_mont(word *, const word *, const word *, const word *, const word *, int);
int bn_mulx4x_mont(word *, const word *, const word *, const word *, const word *, int);
int OPENSSL_init_crypto(unsigned long, const void *);

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1e9 + ts.tv_nsec;
}

static void taint(void *p, size_t bytes, word flags)
{
    zunsafe_fast_call("zeg_request", flags ? 1ul : 2ul, p, bytes, flags);
}

/* Independent schoolbook product modulo M = 2^(64*n)-1. Montgomery R
   is 1 modulo M, so this is also the expected Montgomery product. */
static void reference(word *r, const word *a, const word *b, int n)
{
    word p[64] = {0};
    for (int i = 0; i < n; ++i) {
        word carry = 0;
        for (int j = 0; j < n; ++j) {
            unsigned __int128 t = (unsigned __int128)a[i] * b[j] + p[i+j] + carry;
            p[i+j] = t;
            carry = t >> 64;
        }
        p[i+n] = carry;
    }
    word carry = 0;
    for (int i = 0; i < n; ++i) {
        unsigned __int128 t = (unsigned __int128)p[i] + p[i+n] + carry;
        r[i] = t;
        carry = t >> 64;
    }
    while (carry) {
        for (int i = 0; i < n; ++i) {
            unsigned __int128 t = (unsigned __int128)r[i] + carry;
            r[i] = t;
            carry = t >> 64;
        }
    }
    int all_ones = 1;
    for (int i = 0; i < n; ++i) all_ones &= r[i] == ~0ul;
    if (all_ones) memset(r, 0, n * sizeof *r);
}

static void mont(int adx, word flags, int timing)
{
    int n = adx ? 32 : 17;
    word a[32], b[32], modulus[32], r[32], expected[32], n0 = 1;
    for (int i = 0; i < n; ++i) {
        a[i] = 0xfedcba9876543210ul + i * 1000003ul;
        b[i] = 0x123456789abcdef0ul - i * 99991ul;
        modulus[i] = ~0ul;
    }
    reference(expected, a, b, n);
    taint(a, n * 8, flags);
    taint(b, n * 8, flags);
    int rounds = timing ? 20000 : 1;
    double start = timing ? now() : 0;
    for (int i = 0; i < rounds; ++i) {
        int ok = adx ? bn_mulx4x_mont(r, a, b, modulus, &n0, n)
                     : bn_mul_mont(r, a, b, modulus, &n0, n);
        if (!ok) abort();
    }
    double elapsed = timing ? now() - start : 0;
    taint(r, n * 8, 0);
    taint(a, n * 8, 0);
    taint(b, n * 8, 0);
    if (memcmp(r, expected, n * 8)) {
        fprintf(stderr, "Montgomery result mismatch, adx=%d\n", adx);
        exit(1);
    }
    const char *name = adx ? "bn_mulx4x_mont" : "bn_mul_mont";
    if (timing) printf("%s n=%d %.2f ns/call; result checked\n", name, n, elapsed / rounds);
    else printf("%s result checked\n", name);
}

static void addsub(int sub, word flags, int timing)
{
    enum { n = 512 };
    word a[n], b[n], r[n], expected[n], carry = 0;
    for (int i = 0; i < n; ++i) {
        a[i] = sub ? (i % 3 ? 0 : ~0ul) : ~0ul - i;
        b[i] = i * 3ul + 1;
        if (sub) {
            unsigned __int128 rhs = (unsigned __int128)b[i] + carry;
            expected[i] = a[i] - rhs;
            carry = a[i] < rhs;
        } else {
            unsigned __int128 sum = (unsigned __int128)a[i] + b[i] + carry;
            expected[i] = sum;
            carry = sum >> 64;
        }
    }
    taint(a, sizeof a, flags);
    taint(b, sizeof b, flags);
    word got[1];
    int rounds = timing ? 100000 : 1;
    double start = timing ? now() : 0;
    for (int i = 0; i < rounds; ++i)
        got[0] = sub ? bn_sub_words(r, a, b, n) : bn_add_words(r, a, b, n);
    double elapsed = timing ? now() - start : 0;
    taint(got, sizeof got, 0);
    taint(r, sizeof r, 0);
    taint(a, sizeof a, 0);
    taint(b, sizeof b, 0);
    if (got[0] != carry || memcmp(r, expected, sizeof r)) abort();
    const char *name = sub ? "bn_sub_words" : "bn_add_words";
    if (timing) printf("%s %.2f ns/word; result checked\n", name, elapsed / rounds / n);
    else printf("%s result checked\n", name);
}

int main(int argc, char **argv)
{
    if (!OPENSSL_init_crypto(0, NULL)) abort();
    int timing = argc == 2 && !strcmp(argv[1], "bench");
    if (!timing && (argc != 3 || strcmp(argv[1], "check"))) return 2;
    word flags = timing ? 0 : strtoul(argv[2], NULL, 0);
    addsub(0, flags, timing);
    addsub(1, flags, timing);
    mont(0, flags, timing);
    mont(1, flags, timing);
    return 0;
}

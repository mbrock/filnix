/* glibc's generic memcmp took the addresses of two locals in memcmp_bytes,
   so under Fil-C every memcmp and bcmp call heap-allocated them: a third of
   all allocation in PHP serving WordPress. Check memcmp and bcmp against a
   byte-by-byte reference at every alignment pair, length up to 72 and
   mismatch position, on ranges that end at the object's upper bound (heap
   and global), then check that two million calls start no GC cycle. */
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>

static int (*volatile cmp)(const void *, const void *, size_t) = memcmp;
static int (*volatile bcmp_)(const void *, const void *, size_t) = bcmp;

static unsigned char ga[88], gb[88];

static int ref(const unsigned char *a, const unsigned char *b, size_t n)
{
    for (size_t i = 0; i < n; i++)
        if (a[i] != b[i])
            return a[i] - b[i];
    return 0;
}

static int sign(int x) { return (x > 0) - (x < 0); }

static void check(const unsigned char *a, const unsigned char *b, size_t n, int which)
{
    int r = ref(a, b, n), m = cmp(a, b, n), z = bcmp_(a, b, n);
    if (sign(m) != sign(r) || (!r) != (!z)) {
        printf("FAIL %d n=%zu ref=%d memcmp=%d bcmp=%d\n", which, n, r, m, z);
        exit(1);
    }
}

/* Compare the last n bytes of two buffers of size cap, starting at
   offsets chosen so the ranges end exactly at cap. */
static void sweep(unsigned char *a, unsigned char *b, size_t cap, int which)
{
    for (size_t n = 0; n <= 72; n++)
        for (size_t ea = 0; ea < 8; ea++)
            for (size_t eb = 0; eb < 8; eb++) {
                if (n + ea > cap || n + eb > cap)
                    continue;
                unsigned char *pa = a + cap - n - ea, *pb = b + cap - n - eb;
                for (size_t i = 0; i < n; i++)
                    pa[i] = pb[i] = (unsigned char)(i * 37 + n);
                check(pa, pb, n, which);
                for (size_t k = 0; k < n; k++) {
                    unsigned char save = pb[k];
                    pb[k] = (unsigned char)(save + 1 + (k & 0x7f));
                    check(pa, pb, n, which);
                    check(pb, pa, n, which);
                    pb[k] = save;
                }
            }
}

int main(void)
{
    /* Sizes that are not multiples of 8 or 16, so the ends are odd. */
    for (size_t cap = 80; cap <= 88; cap++) {
        unsigned char *a = malloc(cap), *b = malloc(cap);
        sweep(a, b, cap, 0);
        free(a);
        free(b);
    }
    sweep(ga, gb, sizeof ga, 1);

    unsigned char *x = malloc(4096), *y = malloc(4096);
    for (int i = 0; i < 4096; i++)
        x[i] = y[i] = (unsigned char)i;
    y[4000] ^= 1;
    zgc_request_and_wait();
    zgc_cycle_number before = zgc_requested_cycle();
    long acc = 0;
    for (int i = 0; i < 2000000; i++) {
        size_t off = i & 15, n = 16 + (i & 63);
        acc += cmp(x + off, y + off + (i & 1), n) + bcmp_(x, y, 4096);
    }
    zgc_cycle_number after = zgc_requested_cycle();
    printf("gc cycles requested during memcmp loop: %llu (acc %ld)\n",
           after - before, acc & 1);
    if (after != before) {
        printf("FAIL memcmp allocates\n");
        return 1;
    }
    printf("memcmp noalloc ok\n");
    return 0;
}

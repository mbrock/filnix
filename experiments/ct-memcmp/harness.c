/* Calls the two kernels of memcmp.s (or memcmp.ir) from Fil-C.

     harness table
         print K(a, b, len) for a fixed list of cases; every build must
         print the same lines
     harness ct|leaky SIZE LEN AT [FLAGS]
         two SIZE-byte buffers with the same bytes, byte AT of the second
         changed when 0 <= AT < SIZE, both poisoned with FLAGS (zegarmistrz
         poison bits, 0 by default) while K(a, b, LEN) runs; prints the
         result
     harness bench
         nanoseconds per byte of each kernel on two equal 4096-byte
         buffers

   Built with -DUNCHECKED the kernels are plain assembly, reached with
   zunsafe_fast_call (which needs -yolo-assembler). Otherwise they are
   Fil-C functions: memcmp.s through SaRCAsm, or memcmp.ir through
   nanofil. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdfil.h>

#ifdef UNCHECKED
static int ct_memcmp(const void *a, const void *b, size_t n)
{
    return (int)zunsafe_fast_call("ct_memcmp", a, b, n);
}
static int leaky_memcmp(const void *a, const void *b, size_t n)
{
    return (int)zunsafe_fast_call("leaky_memcmp", a, b, n);
}
#else
int ct_memcmp(const void *a, const void *b, size_t n);
int leaky_memcmp(const void *a, const void *b, size_t n);
#endif

/* zegarmistrz.h's requests; see zeg.s. */
static void poison(void *p, size_t n, unsigned long flags)
{
    zunsafe_fast_call("zeg_request", 1ul, p, n, flags);
}
static void unpoison(void *p, size_t n)
{
    zunsafe_fast_call("zeg_request", 2ul, p, n, 0ul);
}

static unsigned char *buffer(size_t size)
{
    unsigned char *p = malloc(size ? size : 1);
    for (size_t i = 0; i < size; i++)
        p[i] = (unsigned char)(i * 37 + 11);
    return p;
}

static int run(int leaky, long size, long len, long at, unsigned long flags)
{
    unsigned char *a = buffer(size), *b = buffer(size);
    /* The result is as secret as the buffers: it goes to memory, and
       that memory is declassified before anything looks at it. */
    int *result = malloc(sizeof *result);
    if (at >= 0 && at < size)
        b[at] ^= 0x80;
    if (flags) {
        poison(a, size, flags);
        poison(b, size, flags);
    }
    *result = leaky ? leaky_memcmp(a, b, len) : ct_memcmp(a, b, len);
    if (flags) {
        unpoison(result, sizeof *result);
        unpoison(a, size);
        unpoison(b, size);
    }
    return *result;
}

static const long cases[][3] = {
    { 16, 16, -1 }, { 16, 16, 0 }, { 16, 16, 7 }, { 16, 16, 8 }, { 16, 16, 15 },
    { 16, 0, 3 }, { 32, 1, -1 }, { 32, 1, 0 }, { 32, 5, 4 }, { 32, 5, 5 },
    { 32, 15, 14 }, { 32, 17, 16 }, { 32, 17, 0 }, { 32, 32, 31 }, { 64, 64, 33 },
    { 300, 300, -1 }, { 300, 300, 299 }, { 300, 256, 0 }, { 300, 257, 256 },
};

static double ns_per_byte(int leaky)
{
    enum { size = 4096, rounds = 20000 };
    unsigned char *a = buffer(size), *b = buffer(size);
    struct timespec t0, t1;
    int sum = 0;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < rounds; i++)
        sum += leaky ? leaky_memcmp(a, b, size) : ct_memcmp(a, b, size);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    if (sum)
        abort();
    return ((t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec)) / ((double)size * rounds);
}

int main(int argc, char **argv)
{
    if (argc == 2 && !strcmp(argv[1], "bench")) {
        printf("ct %.2f leaky %.2f\n", ns_per_byte(0), ns_per_byte(1));
        return 0;
    }
    if (argc == 2 && !strcmp(argv[1], "table")) {
        for (size_t i = 0; i < sizeof cases / sizeof *cases; i++) {
            const long *c = cases[i];
            printf("%ld %ld %ld: ct %d leaky %d\n", c[0], c[1], c[2],
                   run(0, c[0], c[1], c[2], 0), run(1, c[0], c[1], c[2], 0));
        }
        return 0;
    }
    if (argc < 5 || (strcmp(argv[1], "ct") && strcmp(argv[1], "leaky"))) {
        fprintf(stderr, "usage: %s table | bench | ct|leaky SIZE LEN AT [FLAGS]\n", argv[0]);
        return 2;
    }
    printf("%d\n", run(!strcmp(argv[1], "leaky"), atol(argv[2]), atol(argv[3]),
                       atol(argv[4]), argc > 5 ? strtoul(argv[5], 0, 0) : 0));
    return 0;
}

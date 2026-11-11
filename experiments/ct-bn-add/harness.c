/* Calls the three kernels of bn_add.s (or the IR lifted from it) from
   Fil-C.

     harness add|sub|leaky SIZE N A0 ASTEP B0 BSTEP [FLAGS]
         three SIZE-word buffers r, a and b; a holds A0, A0 + ASTEP, ...
         and b likewise, both poisoned with FLAGS (zegarmistrz poison
         bits, 0 by default) while K(r, a, b, N) runs; prints the carry
         folded with the N words of r, which is what drive.ir's drive_K
         returns for the same six numbers
     harness bench
         nanoseconds per word of each kernel on 512-word buffers

   Built with -DUNCHECKED the kernels are plain assembly, reached with
   zunsafe_fast_call (which needs -yolo-assembler). Otherwise they are
   Fil-C functions: bn_add.s through SaRCAsm, or its lifted IR through
   nanofil. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdfil.h>

typedef unsigned long word;

#ifdef UNCHECKED
static word bn_add_words(word *r, const word *a, const word *b, size_t n)
{
    return zunsafe_fast_call("bn_add_words", r, a, b, n);
}
static word bn_sub_words(word *r, const word *a, const word *b, size_t n)
{
    return zunsafe_fast_call("bn_sub_words", r, a, b, n);
}
static word leaky_add_words(word *r, const word *a, const word *b, size_t n)
{
    return zunsafe_fast_call("leaky_add_words", r, a, b, n);
}
#else
word bn_add_words(word *r, const word *a, const word *b, size_t n);
word bn_sub_words(word *r, const word *a, const word *b, size_t n);
word leaky_add_words(word *r, const word *a, const word *b, size_t n);
#endif

static word kernel(const char *k, word *r, const word *a, const word *b, size_t n)
{
    if (!strcmp(k, "add"))
        return bn_add_words(r, a, b, n);
    if (!strcmp(k, "sub"))
        return bn_sub_words(r, a, b, n);
    return leaky_add_words(r, a, b, n);
}

/* zegarmistrz.h's requests; see ../ct-memcmp/zeg.s. */
static void poison(void *p, size_t n, unsigned long flags)
{
    zunsafe_fast_call("zeg_request", 1ul, p, n, flags);
}
static void unpoison(void *p, size_t n)
{
    zunsafe_fast_call("zeg_request", 2ul, p, n, 0ul);
}

static word *buffer(size_t size, word first, word step)
{
    word *p = malloc((size ? size : 1) * sizeof *p);
    for (size_t i = 0; i < size; i++)
        p[i] = first + i * step;
    return p;
}

static word run(const char *k, size_t size, size_t n, word a0, word astep, word b0, word bstep,
                unsigned long flags)
{
    word *r = buffer(size, 0, 0), *a = buffer(size, a0, astep), *b = buffer(size, b0, bstep);
    /* The carry is as secret as the operands: it goes to memory, and
       that memory is declassified before anything looks at it. */
    word *carry = malloc(sizeof *carry);
    if (flags) {
        poison(a, size * sizeof *a, flags);
        poison(b, size * sizeof *b, flags);
    }
    *carry = kernel(k, r, a, b, n);
    if (flags) {
        unpoison(carry, sizeof *carry);
        unpoison(r, size * sizeof *r);
        unpoison(a, size * sizeof *a);
        unpoison(b, size * sizeof *b);
    }
    word h = *carry;
    for (size_t i = 0; i < n && i < size; i++)
        h = h * 1000003 + r[i];
    return h;
}

static double ns_per_word(const char *k)
{
    enum { size = 512, rounds = 100000 };
    word *r = buffer(size, 0, 0), *a = buffer(size, -3, 1), *b = buffer(size, 1, 1);
    struct timespec t0, t1;
    word sum = 0;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int i = 0; i < rounds; i++)
        sum += kernel(k, r, a, b, size);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    if (sum > rounds)
        abort();
    return ((t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec)) / ((double)size * rounds);
}

int main(int argc, char **argv)
{
    if (argc == 2 && !strcmp(argv[1], "bench")) {
        printf("add %.2f sub %.2f leaky %.2f\n", ns_per_word("add"), ns_per_word("sub"),
               ns_per_word("leaky"));
        return 0;
    }
    if (argc < 8 || (strcmp(argv[1], "add") && strcmp(argv[1], "sub") && strcmp(argv[1], "leaky"))) {
        fprintf(stderr, "usage: %s bench | add|sub|leaky SIZE N A0 ASTEP B0 BSTEP [FLAGS]\n", argv[0]);
        return 2;
    }
    printf("%lu\n", run(argv[1], strtoul(argv[2], 0, 0), strtoul(argv[3], 0, 0), strtoul(argv[4], 0, 0),
                        strtoul(argv[5], 0, 0), strtoul(argv[6], 0, 0), strtoul(argv[7], 0, 0),
                        argc > 8 ? strtoul(argv[8], 0, 0) : 0));
    return 0;
}

/* Small memmove and memset copy payload bytes with libc from 16 bytes up
   (the fork's libpas). Check every size from 1 to 48 bytes at every
   alignment, overlapping in both directions, between objects that hold
   pointers (aux) and objects that do not, against a byte-by-byte reference.
   Pointers in words the operation did not touch must still work, and
   pointers it copied must still work at their new place. Then copy into
   fresh objects while another thread stores pointers into them, so their
   aux is created during the copy, with the GC running. */
#include <pthread.h>
#include <stdatomic.h>
#include <stdfil.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define WORDS 12
#define BYTES (WORDS * 8)

static int targets[WORDS];

static void fail(const char *what, int a, int b, int c)
{
    printf("FAIL %s %d %d %d\n", what, a, b, c);
    exit(1);
}

/* Fill an object with a byte pattern, then put pointers in its even
   words when with_ptrs. */
static void fill(void **obj, int seed, int with_ptrs)
{
    unsigned char *p = (unsigned char *)obj;
    for (int i = 0; i < BYTES; i++)
        p[i] = (unsigned char)(seed * 31 + i * 7 + 1);
    if (with_ptrs)
        for (int w = 0; w < WORDS; w += 2)
            obj[w] = &targets[w];
}

static void ref_move(unsigned char *dst, const unsigned char *src, size_t n)
{
    unsigned char tmp[BYTES];
    for (size_t i = 0; i < n; i++)
        tmp[i] = src[i];
    for (size_t i = 0; i < n; i++)
        dst[i] = tmp[i];
}

/* Words of dst the copy covered whole, that hold a pointer in the
   reference, must dereference to it. A partly overwritten pointer word keeps
   its address bits but loses its capability, as it should. */
static void check_ptrs(void **obj, unsigned char *ref, const char *what, int n, int d, int s)
{
    for (int w = 0; w < WORDS; w++) {
        if (w * 8 < d || w * 8 + 8 > d + n)
            continue;
        void *expect;
        memcpy(&expect, ref + w * 8, 8);
        for (int t = 0; t < WORDS; t++)
            if (expect == &targets[t] && obj[w] == expect && *(int *)obj[w] != t)
                fail(what, n, d, s);
    }
}

static void sweep(int dst_ptrs, int src_ptrs, int same)
{
    for (int n = 1; n <= 48; n++)
        for (int d = 0; d < 16; d++)
            for (int s = 0; s < 16; s++) {
                void **dst = malloc(BYTES);
                void **src = same ? dst : malloc(BYTES);
                fill(dst, 1, dst_ptrs);
                if (!same)
                    fill(src, 2, src_ptrs);
                unsigned char ref[BYTES];
                memcpy(ref, dst, BYTES);
                ref_move(ref + d, (unsigned char *)src + s, n);
                memmove((char *)dst + d, (char *)src + s, n);
                if (memcmp(dst, ref, BYTES))
                    fail(same ? "overlap-bytes" : "move-bytes", n, d, s);
                /* Untouched pointer words still work. */
                for (int w = 0; w < WORDS; w += 2)
                    if (dst_ptrs && (w * 8 + 8 <= d || w * 8 >= d + n)
                        && *(int *)dst[w] != w)
                        fail("untouched-ptr", n, d, s);
                /* Whole pointers moved word to word still work. */
                if (((d - s) & 7) == 0)
                    check_ptrs(dst, ref, "moved-ptr", n, d, s);
                if (!same)
                    free(src);
                free(dst);
            }
}

static void sweep_memset(int with_ptrs)
{
    for (int n = 1; n <= 48; n++)
        for (int d = 0; d < 16; d++) {
            void **obj = malloc(BYTES);
            fill(obj, 3, with_ptrs);
            unsigned char ref[BYTES];
            memcpy(ref, obj, BYTES);
            for (int i = 0; i < n; i++)
                ref[d + i] = 0xa5;
            memset((char *)obj + d, 0xa5, n);
            if (memcmp(obj, ref, BYTES))
                fail("set-bytes", n, d, with_ptrs);
            for (int w = 0; w < WORDS; w += 2)
                if (with_ptrs && (w * 8 + 8 <= d || w * 8 >= d + n) && *(int *)obj[w] != w)
                    fail("set-untouched-ptr", n, d, 0);
            free(obj);
        }
}

/* Concurrent aux creation: for each fresh object, a second thread stores
   pointers into words 0-5 while the main thread memmoves 16-48 bytes into
   words 6-11, from a source with or without pointers, so both may create
   the object's aux at once. After the store thread acknowledges, every
   stored and copied pointer must still carry its capability. */
#define ROUNDS 50000
static void **_Atomic current;
static atomic_int published, acked;

static void *storer(void *arg)
{
    (void)arg;
    for (int round = 1; round <= ROUNDS; round++) {
        while (atomic_load(&published) != round)
            ;
        void **obj = atomic_load(&current);
        for (int w = 0; w < WORDS / 2; w++)
            obj[w] = &targets[w];
        atomic_store(&acked, round);
    }
    return NULL;
}

static void concurrent(void)
{
    pthread_t t;
    pthread_create(&t, NULL, storer, NULL);
    void **src_ptrs = malloc(BYTES);
    void **src_ints = malloc(BYTES);
    fill(src_ptrs, 4, 1);
    fill(src_ints, 5, 0);
    for (int round = 1; round <= ROUNDS; round++) {
        void **obj = malloc(BYTES);
        atomic_store(&current, obj);
        atomic_store(&published, round);
        int n = 16 + round % 33;
        void **src = (round & 1) ? src_ptrs : src_ints;
        memmove(obj + WORDS / 2, src, n);
        while (atomic_load(&acked) != round)
            ;
        if (memcmp(obj + WORDS / 2, src, n))
            fail("concurrent-bytes", round, n, 0);
        if (round & 1)
            for (int w = 0; w * 8 + 8 <= n; w += 2)
                if (*(int *)obj[WORDS / 2 + w] != w)
                    fail("concurrent-copied-ptr", round, n, w);
        for (int w = 0; w < WORDS / 2; w++)
            if (*(int *)obj[w] != w)
                fail("concurrent-stored-ptr", round, w, 0);
        if (round % 10000 == 0)
            zgc_request_and_wait();
    }
    pthread_join(t, NULL);
}

int main(void)
{
    for (int t = 0; t < WORDS; t++)
        targets[t] = t;
    for (int dp = 0; dp < 2; dp++)
        for (int sp = 0; sp < 2; sp++)
            sweep(dp, sp, 0);
    sweep(1, 1, 1);
    sweep(0, 0, 1);
    zgc_request_and_wait();
    sweep_memset(0);
    sweep_memset(1);
    concurrent();
    printf("payload memops ok\n");
    return 0;
}

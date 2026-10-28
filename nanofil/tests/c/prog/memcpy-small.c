// link: lib/memcpy-small.c
/* Small constant memcpy and memmove (docs/perf.md item 7a). Every size
   from 1 to 16 at every pair of misalignments, copying and overlapping in
   both directions, against a byte-by-byte copy; copies that must take
   the runtime's path (pointers, a destination with aux, a global holding
   pointers, objects from clang-built code); and the sizes and forms that
   keep the call. tests/memcpy.sh runs the failing cases. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib/memcpy-small.h"

static unsigned char buf[64], want[64];
static int bad;

static void fill(void)
{
    for (int i = 0; i < 64; i++)
        buf[i] = want[i] = (unsigned char)(i * 7 + 3);
}

static void naive_move(unsigned char *d, const unsigned char *s, int n)
{
    unsigned char t[32];
    for (int i = 0; i < n; i++) t[i] = s[i];
    for (int i = 0; i < n; i++) d[i] = t[i];
}

static void same(const char *what, int n, int a, int b)
{
    if (memcmp(buf, want, sizeof buf)) {
        printf("bad %s %d %d %d\n", what, n, a, b);
        bad++;
    }
}

#define TRY(N)                                                          \
    for (int a = 0; a < 8; a++)                                         \
        for (int b = 0; b < 8; b++) {                                   \
            fill(); memcpy(buf + 24 + a, buf + b, N);                   \
            naive_move(want + 24 + a, want + b, N); same("cpy", N, a, b); \
            fill(); memmove(buf + a, buf + 4 + b, N);                   \
            naive_move(want + a, want + 4 + b, N); same("down", N, a, b); \
            fill(); memmove(buf + 4 + a, buf + b, N);                   \
            naive_move(want + 4 + a, want + b, N); same("up", N, a, b); \
        }

static struct holder global_holder;

int main(void)
{
    TRY(1) TRY(2) TRY(3) TRY(4) TRY(5) TRY(6) TRY(7) TRY(8)
    TRY(9) TRY(10) TRY(11) TRY(12) TRY(13) TRY(14) TRY(15) TRY(16)

    /* A pointer copied by memcpy keeps its capability (source with aux). */
    char *x = malloc(4);
    strcpy(x, "abc");
    char *y;
    memcpy(&y, &x, 8);
    printf("%s\n", y);

    /* Into a global holding pointers (destination with aux), beside the
       pointer it holds. */
    global_holder.p = x;
    long v = 42;
    memcpy(&global_holder.n, &v, 8);
    printf("%s %ld\n", global_holder.p, global_holder.n);

    /* Holders made by clang-built code: whole and in part. */
    struct holder *h = lib_make("hello", 3, "xy");
    struct holder *k = lib_make("a", 1, "b");
    memcpy(k, h, 16);
    memcpy(&k->q, &h->q, 8);
    long n;
    memcpy(&n, &h->n, 8);
    printf("%ld %ld %ld\n", lib_check(k), lib_check(h), n);

    /* A read-only string literal as the source; the result is the
       destination, with its bounds. */
    char *r = memcpy(buf, "abcdefgh", 8);
    printf("%.8s %c\n", (char *)buf, r[63] ? 'y' : 'n');

    /* The same object, and sizes and forms that keep the call. */
    memmove(buf, buf, 16);
    memcpy(buf, "", 0);
    memcpy(buf, "0123456789abcdefg", 17);
    volatile int m = 5;
    memcpy(buf + 17, "ZYXWV", m);
    __builtin___memcpy_chk(buf + 22, "chk!", 4, (size_t)-1);
    printf("%.26s\n", (char *)buf);

    printf("%d bad\n", bad);
    return bad != 0;
}

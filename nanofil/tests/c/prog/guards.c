/* Range guards (docs/m7.md, round 5) that pass, fail and are skipped,
   compared with filcc. Under --checks=guard: a 256-byte table indexed by
   a byte (the guard passes exactly), a signed byte around a centre
   pointer, zero-trip loops, nested loops, a guard kept across calls,
   several guarded accesses in a block, the round-4 renew of a guarded
   proof, and guarded pointer stores after forced collections. check.nix
   runs it under FUGC_SCRIBBLE=1 FUGC_VERIFY=1. */
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
struct N { struct N *next; long v; };
struct T { int n; int k; struct N *slot[4]; unsigned char tab[256]; };
static int calls;
static void __attribute__((noinline)) tick(void) { calls++; }
static long __attribute__((noinline)) bytes(const unsigned char *t, const unsigned char *in, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) { s += t[in[i]]; tick(); }
    return s;
}
static long __attribute__((noinline)) centred(const signed char *in, const int *mid, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) s += mid[in[i]];
    return s;
}
static long __attribute__((noinline)) fields(struct T *t, int n) {
    long s = 0;
    if (n > 2) s = 1;
    for (int i = 0; i < n; i++) {
        s += t->n + t->k;
        t->k = (int)s & 7;
        s += t->tab[(i * 7) & 255];
        for (int j = 0; j < 3; j++) s += t->tab[j];
    }
    return s;
}
// Facts from before the loop reach the else arm across the guard at the
// end of the loop's dominator, which must keep them.
static long __attribute__((noinline)) either(struct T *t, int n) {
    long s = t->n;
    if (n > 0) {
        for (int i = 0; i < n; i++) s += t->tab[i & 15];
    } else {
        s += t->n * 3;
    }
    return s;
}
// Failing guards (the spans are 32 bytes, the object 16: q->a[3] never
// runs), whose accesses run their full checks out of line, one at the
// base itself right after a call, so nothing but the access's own
// flight load holds the base.
struct Q { long a[4]; };
static long __attribute__((noinline)) mixv(long s) { return s * 3 + 1; }
static long __attribute__((noinline)) partial(struct Q *q, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) {
        s = mixv(s);
        s += q->a[0];
        s += q->a[i & 3];
        if (i > 100) s += q->a[3];
    }
    return s;
}
// A loop header with two entries, the arms of an if: the guard goes at
// the end of their common dominator.
static long __attribute__((noinline)) two_entry(const int *a, int n, int odd) {
    long s;
    int i = 0;
    if (odd) s = 1; else s = 2;
    while (i < n) { s += a[i & 7]; i++; }
    return s;
}
static long __attribute__((noinline)) links(struct T *t, int n) {
    for (int i = 0; i < n; i++) {
        struct N *x = malloc(sizeof *x);
        x->v = i;
        x->next = t->slot[i & 3];
        if (i % 8 == 0) zgc_request_and_wait();
        t->slot[i & 3] = x;
    }
    long s = 0;
    for (int k = 0; k < 4; k++)
        for (struct N *p = t->slot[k]; p; p = p->next) s += p->v;
    return s;
}
/* A span whose end passes 2^63 is no span test at all (its ends are
   signed 64-bit): this compiles to plain checks, and its loop never runs. */
static long __attribute__((noinline)) far(const char *a, int n) {
    long s = 0;
    for (int i = 0; i < n; i++) s += *(const long *)(a + 0x7ffffffffffffff8L);
    return s;
}
int main(void) {
    unsigned char *tab = malloc(256);
    for (int i = 0; i < 256; i++) tab[i] = (unsigned char)(i ^ 0x5a);
    unsigned char in[64];
    for (int i = 0; i < 64; i++) in[i] = (unsigned char)(i * 37 + 255);
    int *wide = malloc(256 * sizeof(int));
    for (int i = 0; i < 256; i++) wide[i] = i - 128;
    signed char sin[16];
    for (int i = 0; i < 16; i++) sin[i] = (signed char)(i * 17 - 128);
    struct T *t = calloc(1, sizeof *t);
    t->n = 3;
    for (int i = 0; i < 256; i++) t->tab[i] = (unsigned char)i;
    printf("%ld %ld %d\n", bytes(tab, in, 64), bytes(tab, in, 0), calls);
    printf("%ld %ld\n", centred(sin, wide + 128, 16), centred(sin, wide + 128, -5));
    printf("%ld %ld %ld\n", fields(t, 10), fields(t, 0), fields(t, 1));
    printf("%ld %ld\n", either(t, 20), either(t, 0));
    struct Q *q = malloc(16);
    q->a[0] = 5; q->a[1] = 7;
    printf("%ld %ld\n", partial(q, 2), partial((struct Q *)wide, 9));
    printf("%ld %ld\n", two_entry(wide, 20, 1), two_entry(wide, 3, 0));
    // Guards on an empty object, a freed one and a function, whose loops
    // never run: each span test is 0 and nothing is accessed.
    unsigned char *none = malloc(0), *gone = malloc(64);
    free(gone);
    printf("%ld %ld %ld\n", bytes(none, in, 0), bytes(gone, in, 0),
           bytes((const unsigned char *)(void *)main, in, 0));
    printf("%ld %ld\n", links(t, 100), far((const char *)tab, 0));
    return 0;
}

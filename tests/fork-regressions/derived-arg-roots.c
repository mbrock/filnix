/* Callees root their incoming arguments, and FilPizlonator roots a pointer derived from an
   argument through the argument's frame slot. Each case below reaches its object only through
   pointers derived from an argument after the caller's frame no longer roots it (the caller
   made a musttail call, which pops its frame), across collections, and checks it stays alive. */
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>

struct obj { long tag; struct obj* next; long pad[6]; };

static zweak* w;

static __attribute__((noinline)) void collect(void)
{
    zgc_request_and_wait();
    for (int i = 0; i < 2000; i++) {
        struct obj* q = malloc(sizeof(struct obj));
        q->tag = -1;
    }
    zgc_request_and_wait();
}

static __attribute__((noinline)) struct obj* fresh(long tag)
{
    struct obj* p = malloc(sizeof(struct obj));
    p->tag = tag;
    p->next = NULL;
    return p;
}

static __attribute__((noinline)) long* make(long n)
{
    long* a = malloc(n * sizeof(long));
    for (long i = 0; i < n; i++)
        a[i] = i;
    w = zweak_new(a);
    return a;
}

/* A loop phi rooted at the argument p, which the loop never uses itself. */
static __attribute__((noinline)) long walkarg(long* p, long n)
{
    long* end = p + n;
    long s = 0;
    for (long* q = p; q != end; q++) {
        if (!((end - q) % 16)) {
            struct obj* o = fresh(1);
            collect();
            s += o->tag - 1;
        }
        s += *q;
    }
    ZASSERT(zweak_get(w));
    return s;
}

static __attribute__((noinline)) long viawalk(long* unused, long n)
{
    long* a = make(n);
    __attribute__((musttail)) return walkarg(a, n);
}

/* An interior pointer outlives the argument it comes from; o would take the argument's slot. */
static __attribute__((noinline)) long interiorarg(long* p, long n)
{
    long* mid = p + 8;
    struct obj* o = fresh(5);
    collect();
    ZASSERT(zweak_get(w));
    return *mid + mid[n & 1] + o->tag - 5;
}

static __attribute__((noinline)) long viainterior(long* unused, long n)
{
    long* a = make(n);
    __attribute__((musttail)) return interiorarg(a, n);
}

/* A select between two pointers derived from the argument. */
static __attribute__((noinline)) long selectarg(long* p, long n)
{
    long* q = (n & 1) ? p + 1 : p + 5;
    struct obj* o = fresh(3);
    collect();
    ZASSERT(zweak_get(w));
    return *q + o->tag - 3;
}

static __attribute__((noinline)) long viaselect(long* unused, long n)
{
    long* a = make(n);
    __attribute__((musttail)) return selectarg(a, n);
}

/* A chain of musttail calls, each passing on a pointer derived from its argument. */
static __attribute__((noinline)) long chain2(long* q, long n)
{
    return walkarg(q, n - 4);
}

static __attribute__((noinline)) long chain1(long* p, long n)
{
    long* q = p + 4;
    __attribute__((musttail)) return chain2(q, n);
}

static __attribute__((noinline)) long viachain(long* unused, long n)
{
    long* a = make(n);
    __attribute__((musttail)) return chain1(a, n);
}

/* The same through an indirect musttail call. */
static long (*volatile indirectwalk)(long*, long) = walkarg;

static __attribute__((noinline)) long viaindirect(long* unused, long n)
{
    long* a = make(n);
    long* q = a + 2;
    __attribute__((musttail)) return indirectwalk(q, n - 2);
}

int main(void)
{
    long n = 100;
    long sum = n * (n - 1) / 2;
    ZASSERT(viawalk(NULL, n) == sum);
    ZASSERT(viainterior(NULL, 10) == 8 + 8);
    ZASSERT(viaselect(NULL, 10) == 5);
    ZASSERT(viachain(NULL, n) == sum - (0 + 1 + 2 + 3));
    ZASSERT(viaindirect(NULL, n) == sum - 1);
    printf("ok\n");
    return 0;
}

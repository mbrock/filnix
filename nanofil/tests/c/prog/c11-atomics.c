/* C11 _Atomic objects against clang's (CPython 3.12's pycore_atomic.h
   uses them). A pointer slot declared struct obj *_Atomic is stored by
   plain assignment on one side and loaded by plain reads on the other,
   each direction pairing nanofil with clang (lib/c11-atomics.c): an
   atomic object's loads and stores are atomic, so a pointer's address
   and capability stay one unit, and a torn pair traps. The store-buffer
   litmus then assigns and reads atomic_int flags, sequentially
   consistent without any builtin: without the store's fence both loads
   may see the other's flag still 0. Last, _Atomic(T) specifiers,
   typedefs and members, <stdatomic.h>'s explicit orders, atomic_init,
   fences, and atomic float and double. */
// link: lib/c11-atomics.c
// timeout: 60
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include "lib/c11-atomics.h"

static void *own_store(void *arg)
{
    (void)arg;
    for (int i = 0; i < ROUNDS; i++)
        slot = i & 1 ? large_obj : small_obj;
    return 0;
}

static void *own_load(void *arg)
{
    long sum = 0;
    (void)arg;
    for (int i = 0; i < ROUNDS; i++)
        sum += peer_check(i & 1 ? slot : atomic_load_explicit(&slot, memory_order_relaxed));
    return sum > 0 ? arg : 0;
}

static void *own_litmus(void *arg)
{
    for (int i = 1; i <= LITMUS; i++) {
        SPIN_UNTIL(atomic_load(&round_no) == i);
        flag_a = 1;
        seen_b = flag_b;
        atomic_store_explicit(&done_a, i, memory_order_release);
    }
    return arg;
}

static void litmus(void)
{
    pthread_t a, b;
    int both_zero = 0;
    pthread_create(&a, 0, own_litmus, 0);
    pthread_create(&b, 0, peer_litmus, 0);
    for (int i = 1; i <= LITMUS; i++) {
        atomic_store_explicit(&flag_a, 0, memory_order_relaxed);
        atomic_store_explicit(&flag_b, 0, memory_order_relaxed);
        round_no = i;
        SPIN_UNTIL(done_a == i && done_b == i);
        both_zero += !seen_a && !seen_b;
    }
    pthread_join(a, 0);
    pthread_join(b, 0);
    printf("litmus: %d of %d rounds saw both flags 0\n", both_zero, LITMUS);
}

static void pair(void *(*store)(void *), void *(*load)(void *), const char *what)
{
    pthread_t s, l;
    void *ok;
    slot = small_obj;
    pthread_create(&s, 0, store, 0);
    pthread_create(&l, 0, load, &ok);
    pthread_join(s, 0);
    pthread_join(l, &ok);
    printf("%s: %s\n", what, ok ? "ok" : "no");
}

typedef _Atomic(unsigned char) atomic_byte;
struct counters {
    atomic_byte b;
    _Atomic short s;
    void *_Atomic p;
    _Atomic(double) d;
    _Atomic float f;
};
static struct counters cs = { 1, 2, 0, 0.5, 1.5f };

static long fences(_Atomic long *n, long v)
{
    atomic_thread_fence(memory_order_acquire);
    *n = v;
    atomic_thread_fence(memory_order_seq_cst);
    atomic_signal_fence(memory_order_seq_cst);
    __atomic_thread_fence(__ATOMIC_RELEASE);
    return atomic_load_explicit(n, memory_order_consume);
}

int main(void)
{
    small_obj = malloc(SMALL);
    large_obj = malloc(LARGE);
    small_obj->tag = 1;
    large_obj->tag = 2;
    small_obj->bytes[SMALL - sizeof(long) - 1] = 3;
    large_obj->bytes[LARGE - sizeof(long) - 1] = 4;
    pair(own_store, peer_load, "nanofil stores, clang loads");
    pair(peer_store, own_load, "clang stores, nanofil loads");
    pair(own_store, own_load, "nanofil both");
    litmus();

    printf("sizes %zu %zu %zu %zu, alignments %zu %zu %zu\n",
           sizeof(atomic_byte), sizeof(_Atomic(long)), sizeof cs, sizeof(atomic_bool),
           _Alignof(_Atomic short), _Alignof(atomic_llong), _Alignof(struct counters));
    cs.b = 200;
    cs.s = cs.b + 1;
    cs.p = &cs;
    cs.d = cs.d * 3;
    cs.f = cs.f + cs.d;
    atomic_store_explicit(&cs.s, cs.s * 2, memory_order_relaxed);
    struct counters *self = atomic_load_explicit(&cs.p, memory_order_acquire);
    printf("%d %d %d %g %g\n", cs.b, atomic_load(&cs.s), self == &cs, cs.d, (double)cs.f);
    _Atomic(int *) local;
    int x = 41;
    atomic_init(&local, &x);
    *local += 1;
    atomic_int counted;
    atomic_init(&counted, 9);
    _Atomic long n = 0;
    printf("%d %d %ld\n", *atomic_load(&local), counted, fences(&n, 12));
    fflush(stdout);
    /* An atomic pointer store is still bounds-checked: this slot is past the end. */
    struct obj *_Atomic *past = (struct obj *_Atomic *)small_obj + 2;
    *past = large_obj;
    return 0;
}

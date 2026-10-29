/* Pointer atomics against clang's. One thread stores two objects of
   different sizes into a shared slot with __atomic_store_n while
   another loads it with __atomic_load_n and touches the last byte of
   the object it got; each direction pairs a nanofil side with a clang
   side (lib/atomic-ptr.c). Fil-C's atomic helpers keep a pointer's
   address and capability one unit. A torn pair, one object's address
   with the other's capability, traps. A store-buffer litmus then runs
   a sequentially consistent integer store on each side, nanofil's
   (mov; mfence) against clang's (xchg): without the fence, both loads
   may see the other's flag still 0. Last, pointer loads and stores at
   every order. */
// link: lib/atomic-ptr.c
// timeout: 60
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include "lib/atomic-ptr.h"

static void *own_store(void *arg)
{
    (void)arg;
    for (int i = 0; i < ROUNDS; i++) {
        if (i % 3)
            __atomic_store_n(&slot, i & 1 ? large_obj : small_obj, __ATOMIC_RELEASE);
        else
            __atomic_store_n(&slot, i & 1 ? large_obj : small_obj, __ATOMIC_SEQ_CST);
    }
    return 0;
}

static void *own_load(void *arg)
{
    long sum = 0;
    (void)arg;
    for (int i = 0; i < ROUNDS; i++)
        sum += peer_check(i & 1 ? __atomic_load_n(&slot, __ATOMIC_SEQ_CST)
                                : __atomic_load_n(&slot, __ATOMIC_RELAXED));
    return sum > 0 ? arg : 0;
}

static int counter;

/* Side A of the litmus, and the rounds. */
static void *own_litmus(void *arg)
{
    for (int i = 1; i <= LITMUS; i++) {
        SPIN_UNTIL(__atomic_load_n(&round_no, __ATOMIC_ACQUIRE) == i);
        __atomic_store_n(&flag_a, 1, __ATOMIC_SEQ_CST);
        seen_b = __atomic_load_n(&flag_b, __ATOMIC_SEQ_CST);
        __atomic_store_n(&done_a, i, __ATOMIC_RELEASE);
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
        flag_a = flag_b = 0;
        __atomic_store_n(&round_no, i, __ATOMIC_SEQ_CST);
        SPIN_UNTIL(__atomic_load_n(&done_a, __ATOMIC_ACQUIRE) == i
                   && __atomic_load_n(&done_b, __ATOMIC_ACQUIRE) == i);
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

    __atomic_store_n(&counter, 7, __ATOMIC_SEQ_CST);
    __atomic_store_n(&slot, large_obj, __ATOMIC_RELAXED);
    struct obj *q = __atomic_load_n(&slot, __ATOMIC_CONSUME);
    printf("%d %ld %ld\n", __atomic_load_n(&counter, __ATOMIC_SEQ_CST), q->tag,
           peer_check(__atomic_load_n(&slot, __ATOMIC_SEQ_CST)));
    __atomic_store_n(&slot, 0, __ATOMIC_SEQ_CST);
    printf("%d\n", __atomic_load_n(&slot, __ATOMIC_RELAXED) == 0);
    fflush(stdout);
    /* A pointer atomic is still bounds-checked: this slot is past the end. */
    __atomic_store_n((struct obj **)small_obj + 2, large_obj, __ATOMIC_RELEASE);
    return 0;
}

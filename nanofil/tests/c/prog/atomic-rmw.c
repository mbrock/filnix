/* Atomic read-modify-write against clang (lib/atomic-rmw.c). Eight
   threads, four of them nanofil's and four clang's, hammer one set of
   counters with ++, fetch_add, +=, fetch_sub, a byte that wraps, a
   short counted down, xor toggles, __sync_fetch_and_add, a CAS loop on
   a double and an atomic_flag spinlock: every total is exact only if
   each update is atomic. Then the same split pushes and pops a
   Treiber stack of malloc'd nodes (pointer compare-exchange, weak and
   strong), drained with a pointer exchange: each node is counted once.
   Last, the single-threaded results: the old or new values each
   builtin returns, a failed compare-exchange's expected value, nand,
   __sync_*, atomic_flag, and pointer fetch_add (filcc gives its result
   no capability, so only its address is used). */
// link: lib/atomic-rmw.c
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include "lib/atomic-rmw.h"

static void *own_hammer(void *arg)
{
    long id = (long)arg;
    for (int i = 0; i < ITERS; i++) {
        ++counters.total;
        __c11_atomic_fetch_add(&counters.total, 2, __ATOMIC_SEQ_CST);
        __atomic_add_fetch(&counters.gnu, 1, __ATOMIC_SEQ_CST);
        counters.total += 3;
        atomic_fetch_sub_explicit(&counters.total, 1, memory_order_relaxed);
        counters.wraps += 1;
        counters.down--;
        atomic_fetch_xor(&counters.bits, 1u << (id & 31));
        __sync_add_and_fetch(&counters.gnu, 1);
        counters.sum += 0.5;
        while (atomic_flag_test_and_set(&counters.lock))
            ;
        counters.locked++;
        atomic_flag_clear(&counters.lock);
    }
    return arg;
}

static void own_push(struct node *n)
{
    struct node *old = atomic_load_explicit(&top, memory_order_relaxed);
    do
        n->next = old;
    while (!atomic_compare_exchange_weak_explicit(&top, &old, n, memory_order_release,
                                                  memory_order_relaxed));
}

static struct node *own_pop(void)
{
    struct node *old = atomic_load(&top);
    while (old && !__c11_atomic_compare_exchange_strong(&top, &old, old->next, __ATOMIC_ACQUIRE,
                                               __ATOMIC_ACQUIRE))
        ;
    return old;
}

static void *own_stack(void *arg)
{
    long base = (long)arg * NODES;
    for (int i = 0; i < NODES; i++) {
        struct node *n = malloc(sizeof *n);
        n->payload = base + i;
        (i & 2 ? stack_push : own_push)(n);
        if (i & 1) {
            struct node *got = i & 4 ? stack_pop() : own_pop();
            if (got) {
                popped_sum += got->payload;
                popped_count++;
            }
        }
    }
    return arg;
}

static void run(void *(*own)(void *), void *(*peer)(void *))
{
    pthread_t t[THREADS];
    for (long i = 0; i < THREADS; i++)
        pthread_create(&t[i], 0, i & 1 ? peer : own, (void *)i);
    for (int i = 0; i < THREADS; i++)
        pthread_join(t[i], 0);
}

static _Atomic int ai = 10;
static int pi = 6;
static _Atomic(char) ac = 120;
static _Atomic unsigned long long ull = ~0ull;
static int arr[4] = { 1, 2, 3, 4 };
static _Atomic(int *) cur = arr;
static _Atomic _Bool flag;

int main(void)
{
    run(own_hammer, peer_hammer);
    printf("total %ld (want %ld)\n", (long)counters.total, (long)THREADS * ITERS * 5);
    printf("wraps %d down %d bits %#x gnu %ld sum %g locked %ld\n", counters.wraps,
           counters.down, counters.bits, counters.gnu, (double)counters.sum, counters.locked);

    run(own_stack, peer_stack);
    long sum = popped_sum, count = popped_count;
    for (struct node *n = atomic_exchange(&top, 0); n; n = n->next)
        sum += n->payload, count++;
    long want = (long)THREADS * NODES;
    printf("stack: %ld nodes (want %ld), sum %ld (want %ld), top %p\n", count, want, sum,
           want * (want - 1) / 2, (void *)atomic_load(&top));

    int old = atomic_fetch_add(&ai, 5);
    int now = __c11_atomic_fetch_sub(&ai, 3, __ATOMIC_SEQ_CST);
    printf("fetch %d %d %d", old, now, (int)ai);
    int o = atomic_fetch_or(&ai, 0x100), a = atomic_fetch_and(&ai, 0x10f);
    int x = atomic_fetch_xor(&ai, 3);
    printf(" or %d and %d xor %d", o, a, x);
    o = atomic_exchange(&ai, 77);
    printf(" xchg %d %d\n", o, (int)ai);
    int expected = 5;
    _Bool ok = atomic_compare_exchange_strong(&ai, &expected, 8);
    printf("cas fail %d expected %d", ok, expected);
    ok = atomic_compare_exchange_strong(&ai, &expected, 8);
    printf(" cas ok %d now %d", ok, (int)ai);
    while (!atomic_compare_exchange_weak(&ai, &expected, expected * 3))
        ;
    printf(" weak %d", (int)ai);
    /* *expected is written only on failure (7.17.7.4p2): when it is the
       object itself, a success must leave the new value in place. */
    int self = 4;
    ok = __atomic_compare_exchange_n(&self, &self, 6, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    printf(" self %d %d\n", ok, self);
    int r[5];
    r[0] = __atomic_fetch_add(&pi, 4, __ATOMIC_RELAXED);
    r[1] = __atomic_sub_fetch(&pi, 1, __ATOMIC_ACQ_REL);
    r[2] = __atomic_fetch_nand(&pi, 6, 5);
    r[3] = __atomic_nand_fetch(&pi, 3, 5);
    r[4] = __atomic_exchange_n(&pi, 40, 5);
    printf("plain int: %d %d %d %d %d %d\n", r[0], r[1], r[2], r[3], r[4], pi);
    r[0] = __sync_val_compare_and_swap(&pi, 40, 41);
    r[1] = __sync_bool_compare_and_swap(&pi, 40, 42);
    r[2] = __sync_lock_test_and_set(&pi, 9);
    r[3] = __sync_fetch_and_or(&pi, 16);
    r[4] = __sync_sub_and_fetch(&pi, 5);
    printf("sync: %d %d %d %d %d", r[0], r[1], r[2], r[3], r[4]);
    __sync_lock_release(&pi);
    __sync_synchronize();
    printf(" %d\n", pi);
    r[0] = ac += 10;
    r[1] = ac--;
    printf("char %d %d %d", r[0], r[1], (int)ac);
    unsigned long long u0 = ++ull, u1 = (ull -= 2);
    printf(" ull %llu %llu", u0, u1);
    flag = 1;
    r[0] = atomic_exchange(&flag, 0);
    printf(" bool %d %d\n", r[0], (int)flag);
    atomic_flag f = ATOMIC_FLAG_INIT;
    r[0] = atomic_flag_test_and_set(&f);
    r[1] = atomic_flag_test_and_set(&f);
    atomic_flag_clear(&f);
    r[2] = __atomic_test_and_set(&f, __ATOMIC_SEQ_CST);
    __atomic_clear(&f, __ATOMIC_SEQ_CST);
    r[3] = atomic_flag_test_and_set(&f);
    printf("flag %d %d %d %d\n", r[0], r[1], r[2], r[3]);
    int *before = atomic_fetch_add(&cur, 2);
    cur++;
    int *after = atomic_load(&cur);
    printf("pointer fetch_add: %td then %td, *cur %d\n", before - arr, after - arr, *after);
    fflush(stdout);
    /* A read-modify-write is still bounds-checked: this counter is past the end. */
    _Atomic int *past = (_Atomic int *)arr + 4;
    return atomic_fetch_add(past, 1);
}

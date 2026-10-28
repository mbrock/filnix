/* The clang half of tests/c/prog/atomic-rmw.c: the same hammer and
   Treiber stack, so clang's and nanofil's read-modify-writes race on
   the same objects. */
#include <stdlib.h>
#include "atomic-rmw.h"

struct counters counters = { .sum = 0.0, .lock = ATOMIC_FLAG_INIT };
_Atomic(struct node *) top;
_Atomic long popped_sum, popped_count;

void *peer_hammer(void *arg)
{
    long id = (long)arg;
    for (int i = 0; i < ITERS; i++) {
        counters.total++;
        atomic_fetch_add(&counters.total, 2);
        counters.total += 3;
        __c11_atomic_fetch_sub(&counters.total, 1, __ATOMIC_RELAXED);
        counters.wraps++;
        counters.down -= 1;
        counters.bits ^= 1u << (id & 31);
        __sync_fetch_and_add(&counters.gnu, 1);
        double old = atomic_load(&counters.sum);
        while (!atomic_compare_exchange_weak(&counters.sum, &old, old + 0.5))
            ;
        while (atomic_flag_test_and_set_explicit(&counters.lock, memory_order_acquire))
            ;
        counters.locked++;
        atomic_flag_clear_explicit(&counters.lock, memory_order_release);
    }
    return arg;
}

void stack_push(struct node *n)
{
    struct node *old = atomic_load(&top);
    do
        n->next = old;
    while (!atomic_compare_exchange_weak(&top, &old, n));
}

struct node *stack_pop(void)
{
    struct node *old = atomic_load(&top);
    while (old && !atomic_compare_exchange_strong(&top, &old, old->next))
        ;
    return old;
}

void *peer_stack(void *arg)
{
    long base = (long)arg * NODES;
    for (int i = 0; i < NODES; i++) {
        struct node *n = malloc(sizeof *n);
        n->payload = base + i;
        stack_push(n);
        if (i & 1) {
            struct node *got = stack_pop();
            if (got) {
                atomic_fetch_add(&popped_sum, got->payload);
                atomic_fetch_add(&popped_count, 1);
            }
        }
    }
    return arg;
}

/* clang's side of tests/c/prog/c11-atomics.c, with <stdatomic.h>. */
#include "c11-atomics.h"

struct obj *_Atomic slot;
struct obj *small_obj, *large_obj;
atomic_int flag_a, flag_b, round_no, done_a, done_b;
int seen_a, seen_b;

/* The last byte of the object q claims to be: a torn pair (one object's
   address with the other's capability) traps here. */
long peer_check(struct obj *q)
{
    return q->tag + q->bytes[(q->tag == 2 ? LARGE : SMALL) - sizeof(long) - 1];
}

void *peer_store(void *arg)
{
    (void)arg;
    for (int i = 0; i < ROUNDS; i++)
        atomic_store_explicit(&slot, i & 1 ? large_obj : small_obj,
                              i % 3 ? memory_order_release : memory_order_seq_cst);
    return 0;
}

void *peer_load(void *arg)
{
    long sum = 0;
    (void)arg;
    for (int i = 0; i < ROUNDS; i++)
        sum += peer_check(slot);
    return sum > 0 ? arg : 0;
}

/* Side B of the litmus: clang's seq_cst stores and loads of _Atomic ints. */
void *peer_litmus(void *arg)
{
    for (int i = 1; i <= LITMUS; i++) {
        SPIN_UNTIL(atomic_load_explicit(&round_no, memory_order_acquire) == i);
        flag_b = 1;
        seen_a = flag_a;
        atomic_store_explicit(&done_b, i, memory_order_release);
    }
    return arg;
}

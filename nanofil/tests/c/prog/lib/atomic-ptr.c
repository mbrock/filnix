/* clang's side of tests/c/prog/atomic-ptr.c: a writer and a reader of
   the shared slot with clang's own pointer atomics. */
#include "atomic-ptr.h"

struct obj *slot;
struct obj *small_obj, *large_obj;

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
        __atomic_store_n(&slot, i & 1 ? large_obj : small_obj,
                         i % 3 ? __ATOMIC_RELEASE : __ATOMIC_SEQ_CST);
    return 0;
}

void *peer_load(void *arg)
{
    long sum = 0;
    (void)arg;
    for (int i = 0; i < ROUNDS; i++)
        sum += peer_check(__atomic_load_n(&slot, __ATOMIC_ACQUIRE));
    return sum > 0 ? arg : 0;
}

int flag_a, flag_b, seen_b, seen_a, round_no, done_a, done_b;

/* Side B of the litmus with clang's seq_cst store (xchg). */
void *peer_litmus(void *arg)
{
    for (int i = 1; i <= LITMUS; i++) {
        SPIN_UNTIL(__atomic_load_n(&round_no, __ATOMIC_ACQUIRE) == i);
        __atomic_store_n(&flag_b, 1, __ATOMIC_SEQ_CST);
        seen_a = __atomic_load_n(&flag_a, __ATOMIC_SEQ_CST);
        __atomic_store_n(&done_b, i, __ATOMIC_RELEASE);
    }
    return arg;
}

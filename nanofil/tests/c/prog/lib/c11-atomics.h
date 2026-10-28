/* The _Atomic objects tests/c/prog/c11-atomics.c shares with clang. */
#include <stdatomic.h>
struct obj { long tag; char bytes[]; };
extern struct obj *_Atomic slot;
extern struct obj *small_obj, *large_obj;
enum { SMALL = 16, LARGE = 4096, ROUNDS = 200000, LITMUS = 50000 };
long peer_check(struct obj *q);
void *peer_store(void *arg);
void *peer_load(void *arg);
void *peer_litmus(void *arg);
extern atomic_int flag_a, flag_b, round_no, done_a, done_b;
extern int seen_a, seen_b;

#include <sched.h>
#define SPIN_UNTIL(cond)                                    \
    for (int spins_ = 0; !(cond); spins_++)                 \
        if (spins_ > 1000) sched_yield()

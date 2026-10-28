/* The atomic objects tests/c/prog/atomic-rmw.c shares with clang. */
#include <stdatomic.h>
#include <stdbool.h>

enum { THREADS = 8, ITERS = 20000, NODES = 4000 };

struct counters {
    _Atomic long total;
    _Atomic unsigned char wraps;
    _Atomic short down;
    _Atomic unsigned bits;
    long gnu;
    _Atomic double sum;
    atomic_flag lock;
    long locked;
};
extern struct counters counters;

struct node {
    struct node *next;
    long payload;
};
extern _Atomic(struct node *) top;
extern _Atomic long popped_sum, popped_count;

void *peer_hammer(void *arg);
void *peer_stack(void *arg);
void stack_push(struct node *n);
struct node *stack_pop(void);

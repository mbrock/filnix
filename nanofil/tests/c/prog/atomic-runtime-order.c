/* Memory orders known only at run time, as liburcu passes
   cmm_to_c11(CMM_RELAXED), and __atomic_always_lock_free in a static
   assertion. nanofil evaluates such an order and uses seq_cst. */
#include <stdio.h>

static int calls;
static int to_c11(int mo) { calls++; return mo == 6 ? __ATOMIC_SEQ_CST : mo; }

struct node { struct node *next; };

int main(void)
{
    _Static_assert(__atomic_always_lock_free(sizeof(void *), 0), "pointers");
    _Static_assert(__atomic_always_lock_free(16, 0) && !__atomic_always_lock_free(32, 0), "filcc inlines 16 bytes");
    long l = 0;
    char c[2];
    struct node a = {0}, b = {&a}, *tail = &b;
    int x = 1;
    int v = __atomic_load_n(&x, to_c11(__ATOMIC_ACQUIRE));
    __atomic_store_n(&x, v + 4, to_c11(__ATOMIC_RELEASE));
    struct node *old = __atomic_exchange_n(&tail, &a, to_c11(6));
    int exp = 5;
    int ok = __atomic_compare_exchange_n(&x, &exp, 9, 0, to_c11(6), to_c11(__ATOMIC_RELAXED));
    int prev = __atomic_fetch_add(&x, 3, to_c11(__ATOMIC_RELAXED));
    __atomic_thread_fence(to_c11(6));
    printf("%d %d %d %d %d %d %d\n", v, old == &b, tail == &a, ok, prev, x, calls);
    printf("%d %d %d %d\n", __atomic_always_lock_free(sizeof l, &l), __atomic_always_lock_free(2, c),
           __atomic_always_lock_free(1, c), __atomic_always_lock_free(16, &l));
    return 0;
}

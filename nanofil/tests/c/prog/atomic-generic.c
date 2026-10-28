/* GCC's generic atomics, which pass values through pointers:
   __atomic_load, __atomic_store, __atomic_exchange and
   __atomic_compare_exchange on integers of each width and on pointers,
   and GLib's g_once_init_enter and g_atomic_pointer_get, which use
   them (gthread.h, gatomic.h). Each argument is evaluated once. */
#include <stdio.h>
#include <stddef.h>
static int calls;
static long *where(long *p) { calls++; return p; }
static size_t once_value;
static int once_init_enter(size_t *location)
{
    size_t v;
    __atomic_load(location, &v, __ATOMIC_ACQUIRE);
    return v == 0;
}
int main(void)
{
    long l = 5, r = 0, n = 7;
    __atomic_load(where(&l), &r, __ATOMIC_SEQ_CST);
    printf("load %ld calls %d\n", r, calls);
    __atomic_store(where(&l), &n, __ATOMIC_RELEASE);
    printf("store %ld calls %d\n", l, calls);
    long x = 9, old = 0;
    __atomic_exchange(&l, &x, &old, __ATOMIC_SEQ_CST);
    printf("exchange old %ld now %ld\n", old, l);
    long expected = 1, desired = 11;
    int ok = __atomic_compare_exchange(&l, &expected, &desired, 0, __ATOMIC_SEQ_CST,
                                       __ATOMIC_SEQ_CST);
    printf("cas fail %d expected %ld l %ld\n", ok, expected, l);
    ok = __atomic_compare_exchange(&l, &expected, &desired, 1, __ATOMIC_SEQ_CST,
                                   __ATOMIC_RELAXED);
    printf("cas ok %d expected %ld l %ld\n", ok, expected, l);
    unsigned char c = 200, cr;
    short s = -3, sr;
    __atomic_load(&c, &cr, __ATOMIC_RELAXED);
    __atomic_load(&s, &sr, __ATOMIC_RELAXED);
    printf("narrow %u %d\n", cr, sr);
    int a = 1, b = 2, *pp = &a, *got, *want = &a;
    __atomic_load(&pp, &got, __ATOMIC_ACQUIRE);
    __atomic_compare_exchange(&pp, &want, &(int *){&b}, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    printf("pointer %d %d\n", *got, *pp);
    int *swapped;
    __atomic_exchange(&pp, &(int *){&a}, &swapped, __ATOMIC_SEQ_CST);
    printf("pointer exchange %d %d\n", *swapped, *pp);
    printf("once %d\n", once_init_enter(&once_value));
    once_value = 1;
    printf("once %d\n", once_init_enter(&once_value));
    return 0;
}

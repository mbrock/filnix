// A compare-exchange's expected pointer may be a void *, which converts
// to the object's pointer type as by assignment. GLib's
// g_atomic_int_compare_and_exchange passes `(void *) &old` inside a
// statement expression, and dconf applies `!` to it.
#include <stdio.h>

#define CAS(atomic, oldval, newval)                                        \
    (__extension__({                                                       \
        int old_ = (oldval);                                               \
        _Static_assert(sizeof *(atomic) == sizeof(int), "int");            \
        (void)(0 ? *(atomic) ^ (newval) ^ (oldval) : 1);                   \
        __atomic_compare_exchange_n((atomic), (void *)(&(old_)), (newval), \
                                    0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST) \
            ? 1                                                            \
            : 0;                                                           \
    }))

int main(void) {
    int a = 3;
    _Atomic long c = 7;
    long expect = 8;
    int first = CAS(&a, 3, 5);
    int second = !CAS(&a, 3, 9);
    int third = __c11_atomic_compare_exchange_strong(&c, (void *)&expect, 1, 5, 5);
    printf("%d %d %d %d %ld %ld\n", first, second, a, third, expect, (long)c);
    return 0;
}

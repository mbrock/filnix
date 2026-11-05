// Sealed closures run like closures: the body sees its data through
// zcallee_closure_data, across GC, while ordinary closures keep their API.
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>

struct counter {
    long count;
};

static long bump(long by)
{
    struct counter* counter = zcallee_closure_data();
    counter->count += by;
    return counter->count;
}

static long (*make_counter(void))(long)
{
    struct counter* counter = calloc(1, sizeof(struct counter));
    return zclosure_new_sealed(bump, counter);
}

static void* self(void)
{
    return zcallee();
}

int main(void)
{
    long (*a)(long) = make_counter();
    long (*b)(long) = make_counter();
    for (int i = 0; i < 1000; i++) {
        a(1);
        b(2);
        if (!(i % 100))
            zgc_request_and_wait();
    }
    ZASSERT(a(0) == 1000);
    ZASSERT(b(0) == 2000);

    // The body's own callee is the sealed closure, and it stays callable.
    void* (*s)(void) = zclosure_new_sealed(self, NULL);
    ZASSERT(s() == (void*)s);

    // Unsealed closures are unchanged: readable, writable, rebindable.
    long (*open)(long) = zclosure_new(bump, calloc(1, sizeof(struct counter)));
    open(5);
    ZASSERT(((struct counter*)zclosure_get_data(open))->count == 5);
    struct counter* other = calloc(1, sizeof(struct counter));
    zclosure_set_data(open, other);
    open(7);
    ZASSERT(other->count == 7);
    long (*rebound)(long) = zclosure_new(open, other);
    rebound(1);
    ZASSERT(other->count == 8);

    // An unsealed closure can be sealed by wrapping it; the result is sealed.
    long (*wrapped)(long) = zclosure_new_sealed(open, other);
    ZASSERT(wrapped(2) == 10);

    printf("sealed closures ok\n");
    return 0;
}

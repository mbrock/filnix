/* Two idioms of the SQLite amalgamation. Its AtomicLoad/AtomicStore
   use __atomic_load_n and __atomic_store_n on an int and a pointer, and
   its builtin function table stores small integers cast to pointers,
   SQLITE_INT_TO_PTR(1), in a static initializer (C11 6.6p9). The last
   access dereferences such an integer: both builds trap. */
#include <stdio.h>

struct func { const char *name; void *arg; };
static struct func funcs[] = {
    { "min", ((void *)(long)(0)) },
    { "max", ((void *)(long)(1)) },
    { "neg", ((void *)(long)(-3)) },
};

static int counter;
static int *slot;

int main(void)
{
    int x = 40;
    __atomic_store_n(&counter, 2, __ATOMIC_RELAXED);
    __atomic_store_n(&slot, &x, __ATOMIC_RELEASE);
    int *p = __atomic_load_n(&slot, __ATOMIC_ACQUIRE);
    printf("%d %d\n", __atomic_load_n(&counter, __ATOMIC_RELAXED) + *p,
           __atomic_load_n(&counter, __ATOMIC_SEQ_CST));
    for (unsigned i = 0; i < sizeof funcs / sizeof funcs[0]; i++)
        printf("%s %ld %d\n", funcs[i].name, (long)funcs[i].arg,
               funcs[i].arg == 0);
    fflush(stdout);
    return *(int *)funcs[1].arg;
}

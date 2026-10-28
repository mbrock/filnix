/* An atomic read-modify-write must be aligned to its width, as Fil-C
   checks it: lock cmpxchg on a misaligned address is a split lock.
   The aligned counter at buf+4 works; the one at buf+2, which a plain
   4-byte access could read, traps as filcc's does. */
#include <stdatomic.h>
#include <stdio.h>

static char buf[16] __attribute__((aligned(8)));

int main(void)
{
    _Atomic int *p = (_Atomic int *)(buf + 4);
    atomic_fetch_add(p, 3);
    int expected = 3;
    atomic_compare_exchange_strong(p, &expected, 9);
    printf("aligned: %d\n", (int)*p);
    fflush(stdout);
    p = (_Atomic int *)(buf + 2);
    return atomic_fetch_add(p, 1);
}

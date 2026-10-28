/* GC stress for reuse-gc.ir; run-c.sh runs it with and without
   FUGC_SCRIBBLE=1 FUGC_VERIFY=1, and the Nix check with both
   NANOFIL_CHECKS=reference and reuse. */
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

long survive(long n);
long survive2(long n);
long survive3(long n);

static void *volatile sink;

void c_gc(long i)
{
    sink = malloc(64 + i % 64);
    if (i % 500 == 0)
        zgc_request_and_wait();
    else if (i % 37 == 0)
        zgc_request_fresh();
}

int main(int argc, char **argv)
{
    switch (atoi(argv[1])) {
    case 0: {
        /* sum of 3i - 976 for i < 3000 = 3 * 4498500 - 2928000 */
        long s = 0;
        for (long i = 0; i < 3000; i++)
            s += survive(i);
        printf("survive = %ld\n", s);
        break;
    }
    case 1: {
        /* sum of i + 1001 for i < 3000 = 4498500 + 3003000 */
        long s = 0;
        for (long i = 0; i < 3000; i++)
            s += survive2(i);
        printf("survive2 = %ld\n", s);
        break;
    }
    case 2: {
        /* sum of i + 1001 for i < 3000, as survive2 */
        long s = 0;
        for (long i = 0; i < 3000; i++)
            s += survive3(i);
        printf("survive3 = %ld\n", s);
        break;
    }
    }
    return 0;
}

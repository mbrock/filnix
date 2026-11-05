#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <time.h>
#include <stdfil.h>

#define N 4096
struct arr { char *p[N]; char data[N]; };

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }

static __attribute__((noinline)) long run(struct arr *a, long iters)
{
    long sum = 0;
    for (long it = 0; it < iters; it++)
        for (int i = 0; i < N; i++) {
            a->p[i] = a->data + ((i + it) & (N - 1));
            sum += *a->p[(i * 7) & (N - 1)];
        }
    return sum;
}

static __attribute__((noinline)) long loads(struct arr *a, long iters)
{
    long sum = 0;
    for (long it = 0; it < iters; it++)
        for (int i = 0; i < N; i++)
            sum += (long)a->p[i];
    return sum;
}

int main(int argc, char **argv)
{
    long iters = argc > 1 ? atol(argv[1]) : 2000;
    struct arr *kinds[3];
    const char *names[3] = { "malloc", "MAP_SHARED unmarked", "MAP_SHARED marked" };
    kinds[0] = calloc(1, sizeof(struct arr));
    for (int k = 1; k < 3; k++) {
        kinds[k] = mmap(NULL, sizeof(struct arr), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
#ifdef HAVE_ZMARK
        if (k == 2)
            zmark_shared(kinds[k]);
#endif
    }
    for (int k = 0; k < 3; k++)
        for (int i = 0; i < N; i++)
            kinds[k]->p[i] = kinds[k]->data;
    int only = argc > 2 ? atoi(argv[2]) : -1;
    for (int k = 0; k < 3; k++) {
        if (only >= 0 && k != only)
            continue;
        double t0 = now();
        long s = run(kinds[k], iters);
        double t1 = now();
        long s2 = loads(kinds[k], iters);
        double t2 = now();
        printf("%-20s store+load %.2f ns/op   load %.2f ns/op  (%ld %ld)\n", names[k],
               (t1 - t0) * 1e9 / ((double)iters * N), (t2 - t1) * 1e9 / ((double)iters * N), s & 1, s2 & 1);
    }
    return 0;
}

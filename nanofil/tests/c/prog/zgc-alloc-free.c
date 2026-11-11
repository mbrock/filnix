/* libpizlo allocation is an IR allocation; its free stays an external
   call even inside glibc's free wrapper. Aliases of a freed capability
   must trap, including a second free and an interior-pointer free. */
// run: $probe 0
// run: $probe 1
// run: $probe 2
// run: $probe 3
// run: $probe 4
// run: $probe 5
#include <stdfil.h>
#include <stdio.h>

static int frees;
void free(void *p) { ++frees; zgc_free(p); }

int probe(int mode)
{
    if (mode == 4) { zgc_free(0); free(0); return 41; }
    unsigned char *p = zgc_alloc(mode == 5 ? 0 : 17);
    if (mode == 5) { free(p); return 53; }
    unsigned char *q = p;
    p[0] = 7;
    p[16] = 31;
    int sum = p[0] + p[16];
    if (mode == 3) { zgc_free(p + 1); return 0; }
    int before = frees;
    free(p);
    if (mode == 1) return q[0];
    if (mode == 2) zgc_free(q);
    return sum + (frees - before);
}

int main(void)
{
    printf("%d %d %d\n", probe(0), probe(4), probe(5));
    return 0;
}

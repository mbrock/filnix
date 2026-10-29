/* A packed struct holding a pointer is copied by the runtime's
   capability-aware copy, as filcc copies it, never by a memcpy the
   program defines: this one copies bytes and would drop the pointer's
   capability. A local initializer's null pointer at a misaligned offset
   is bytes, not a pointer store, and a static initializer may put a
   pointer at a multiple of 8 in a packed struct. */
#include <stdio.h>
#include <stdlib.h>
void *memcpy(void *d, const void *s, size_t n)
{
    char *dd = d;
    const char *ss = s;
    for (size_t i = 0; i < n; i++)
        dd[i] = ss[i];
    return d;
}
struct __attribute__((packed)) P { long l; int *p; };
struct __attribute__((packed)) M { char c; int *p; char d[6]; };
static int x = 42;
static struct P gp = { 3, &x };
static const struct P table[2] = { { 1, &x }, { 2, 0 } };
int main(void)
{
    struct P *a = malloc(sizeof *a), *b = malloc(sizeof *b);
    a->p = &x;
    *b = *a;
    struct M m = { 1, 0 };
    printf("%d %d %d %d %d\n", *b->p, m.c, *gp.p, *table[0].p, table[1].p == 0);
    return 0;
}

// link: lib/object-alignment.c
/* _Alignas and GNU aligned(N) on object declarations (CPython's
   socketmodule aligns a char buffer with Py_ALIGNED(8)): globals,
   statics and locals, kept in the frame or passed to clang, and a
   variable length array, each aligned as requested while its type, and
   so sizeof and _Alignof of it, is unchanged. Each object is placed
   after a char to make an unaligned slot likely. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
int misaligned(const void *p, unsigned n);   /* clang's, lib/object-alignment.c */
#define MIS(x, n) ((int)((uintptr_t)(x) % (n)))
char g_pad = 1;
_Alignas(16) char g_buf[24];
char g_pad2 = 2;
char g_attr[5] __attribute__((aligned(8)));
static char s_pad = 3;
static _Alignas(long) char s_buf[3];
_Alignas(0) short g_zero;          /* no effect (C11 6.7.5p6) */
static int sum(int n)
{
    char pad = (char)n;
    _Alignas(16) char local[17];
    char pad2 = 2;
    char attr[3] __attribute__((__aligned__(8)));
    char pad3 = 3;
    _Alignas(double) char escaped[9];
    static _Alignas(16) char st[2];
    char vla[n] __attribute__((aligned(16)));
    memset(local, n, sizeof local);
    memset(vla, 1, (size_t)n);
    escaped[0] = 7;
    printf("locals %d %d %d %d %d\n", MIS(local, 16), MIS(attr, 8), MIS(st, 16),
           MIS(vla, 16), misaligned(escaped, 8));
    printf("sizes %zu %zu %zu\n", sizeof local, sizeof attr, sizeof escaped);
    return pad + pad2 + pad3 + local[16] + vla[n - 1] + escaped[0];
}
int main(void)
{
    printf("globals %d %d %d %d %d\n", MIS(g_buf, 16), MIS(g_attr, 8),
           MIS(s_buf, 8), misaligned(g_buf, 16), misaligned(s_buf, 8));
    printf("%zu %zu %d %d %d %d\n", sizeof g_buf, _Alignof(char), g_pad, g_pad2,
           s_pad, g_zero);
    printf("sum %d\n", sum(5));
    return 0;
}

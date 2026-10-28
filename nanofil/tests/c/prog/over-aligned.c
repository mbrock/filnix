// link: lib/over-aligned.c
/* Alignment above 16: a global, a data object holding pointers (its
   relocations follow the pad before its header), a local that escapes
   to clang, a page-aligned local, a struct with an aligned(32) member
   and an aligned(64) typedef, each aligned as requested on nanofil's
   side, a struct defined aligned(32), a scalar typedef aligned(16) and
   one lowered to aligned(1), which packs a struct member, and clang's objects (lib/over-aligned.c) as aligned on its
   side, each side checking the other's addresses. Fil-C gives an
   object aligned above 16 filc_allocate_with_alignment's storage, or
   pads a global before its header (docs/abi-findings.md). */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "lib/over-aligned.h"
#define MIS(x, n) ((int)((uintptr_t)(x) % (n)))
char g_pad = 1;
int g64 __attribute__((aligned(64))) = 64;
char g_pad2 = 2;
struct ptrs gps __attribute__((aligned(64))) = { "pointer", &g64 };
static _Alignas(128) char s_buf[3] = "ab";
struct member m_glob = { 7, 9 };
struct __attribute__((aligned(32))) s32 { int x; } g_s32 = { 32 };
char g_pad3 = 3;
typedef int i16 __attribute__((aligned(16)));
i16 g_i16 = 16;
typedef int i1 __attribute__((aligned(1)));
struct low { char c; i1 v; } g_low = { 1, 2 };
static int sum(int n)
{
    char pad = (char)n;
    char local[40] __attribute__((aligned(64)));
    char pad2 = 2;
    _Alignas(4096) char page[10];
    struct member m = { 1, 2 };
    line64 l;
    memset(local, n, sizeof local);
    memset(page, 1, sizeof page);
    memset(l.b, 3, sizeof l.b);
    printf("local %d page %d member %d typedef %d\n", MIS(local, 64), MIS(page, 4096),
           MIS(&m.v, 32), MIS(&l, 64));
    printf("clang sees local %d member %d\n", clang_misaligned(local, 64),
           clang_misaligned(&m.v, 32));
    return local[n] + page[9] + pad + pad2 + m.v + l.b[63] + (int)sizeof(struct member)
        + (int)_Alignof(struct member) + (int)sizeof(line64) + (int)_Alignof(line64);
}
static int check(const void *p, unsigned n) { return MIS(p, n); }
int main(void)
{
    printf("g64 %d gps %d s_buf %d m_glob.v %d\n", MIS(&g64, 64), MIS(&gps, 64), MIS(s_buf, 128),
           MIS(&m_glob.v, 32));
    printf("clang sees g64 %d gps %d\n", clang_misaligned(&g64, 64), clang_misaligned(&gps, 64));
    printf("gps %s %d %s\n", gps.s, *gps.p, s_buf);
    printf("clang's c64 %d cps %d %s %d\n", MIS(&c64, 64), MIS(&cps, 64), cps.s, *cps.p);
    printf("clang's local %d\n", clang_local(check));
    printf("s32 %zu %zu %d i16 %zu %zu %d low %zu %zu %zu\n", sizeof(struct s32),
           _Alignof(struct s32), MIS(&g_s32, 32), sizeof(i16), _Alignof(i16), MIS(&g_i16, 16),
           sizeof(struct low), _Alignof(struct low), __builtin_offsetof(struct low, v));
    printf("sum %d\n", sum(5));
    return g_pad + g_pad2 + g_pad3 - 6 + g_low.v - 2;
}

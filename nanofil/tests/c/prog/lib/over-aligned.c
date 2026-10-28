/* clang's side of tests/c/prog/over-aligned.c. */
#include <stdint.h>
#include "over-aligned.h"
char c_pad = 1;
int c64 __attribute__((aligned(64))) = 640;
struct ptrs cps __attribute__((aligned(64))) = { "clang", &c64 };
int clang_misaligned(const void *p, unsigned n) { return (int)((uintptr_t)p % n); }
int clang_local(int (*check)(const void *, unsigned))
{
    char pad = 1;
    _Alignas(256) char buf[5] = { pad };
    return check(buf, 256) + buf[0] - 1;
}

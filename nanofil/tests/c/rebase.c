/* Neighbouring elements: with -O, simplify.pl rebases &a[i + c] on &a[i]
   in the same block where the offset is exact (rebased_op/7), and the
   check passes then share one object's checks between them. The runs
   cross each bound: a 64-bit index, a 32-bit one whose range (w >> 1)
   rules out the wrap, and a negative neighbour, each trapping on the
   second access after the first has happened. */
#include <stddef.h>
#include <stdint.h>

static uint32_t arena[8];

static uint32_t pair64p(uint32_t *a, size_t idx, uint32_t v) {
    a[idx] = 0xFFFFFFFFU;
    a[idx + 1] = v;
    return a[idx] + a[idx + 1];
}

static uint32_t pair32p(uint32_t *a, uint32_t w, uint32_t v) {
    uint32_t idx = w >> 1;
    a[idx] = 0xFFFFFFFFU;
    a[idx + 1] = v;
    return a[idx];
}

uint32_t pair64(size_t idx, uint32_t v) { return pair64p(arena, idx, v); }
uint32_t pair32(uint32_t w, uint32_t v) { return pair32p(arena, w, v); }

int64_t back(int64_t i) {
    int64_t p[4];
    for (int k = 0; k < 4; k++) p[k] = k * 10;
    return p[i] - p[i - 1];
}
// run: $pair64 0 5
// run: $pair64 6 5
// run: $pair64 7 5
// run: $pair32 12 9
// run: $pair32 14 9
// run: $pair32 4294967295 9
// run: $back 1
// run: $back 3
// run: $back 0
// run: $back 4

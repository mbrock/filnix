// Bit-counting builtins of constants fold, so they may initialize a
// static or size an array (rhash's rhash_popcount in algorithms.c).
#include <stdio.h>
static const unsigned a = __builtin_popcount(0x7fffffffu);
static const int b = __builtin_popcountll(0xf0f0ULL) + __builtin_ctz(8)
                     + __builtin_clz(1u) + __builtin_ffs(0) + __builtin_ffsl(-1L);
static const int c = __builtin_popcount(-1) + __builtin_clzll(1ULL << 40);
enum { E = __builtin_popcountl(255UL) };
int main(void) {
    static int arr[__builtin_popcount(3)];
    int local[__builtin_ffs(0x40)];
    printf("%u %d %d %d %zu %zu\n", a, b, c, E, sizeof arr, sizeof local);
    return 0;
}

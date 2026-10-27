/* GNU bit builtins (ctz, clz, popcount for int, long and long long;
   byte swaps), lowered branch-free; lz4 and xxhash use them. */
static unsigned long long vals[] = { 1, 2, 3, 0x80, 0xff00, 0x80000000u, 0x123456789abcdef0ull, 0x8000000000000000ull, 0xffffffffffffffffull, 7 };
long bits(long i)
{
    unsigned long long v = vals[i];
    unsigned u = (unsigned)v ? (unsigned)v : 1;
    return __builtin_ctzll(v) + 100 * __builtin_clzll(v) + 10000 * __builtin_popcountll(v)
         + 1000000L * __builtin_ctz(u) + 100000000L * __builtin_clz(u) + 10000000000L * __builtin_popcount(u)
         + (long)(__builtin_bswap64(v) ^ __builtin_bswap32((unsigned)v) ^ __builtin_bswap16((unsigned short)v))
         + __builtin_ctzl(v) * 3 + __builtin_clzl(v) * 5 + __builtin_popcountl(v) * 7;
}
// run: $bits 0
// run: $bits 1
// run: $bits 2
// run: $bits 3
// run: $bits 4
// run: $bits 5
// run: $bits 6
// run: $bits 7
// run: $bits 8
// run: $bits 9

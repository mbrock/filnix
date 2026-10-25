/* Native M6 diagnostic, not a correctness test or part of the test gate.
   Compile with each backend mode; compare the printed result with filcc
   before timing. Arguments are iteration count and seed. Unsigned chains
   keep every arithmetic result live without overflow or shift UB. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  unsigned long count = argc > 1 ? strtoul(argv[1], 0, 10) : 1000000UL;
  unsigned long seed = argc > 2 ? strtoul(argv[2], 0, 10) : 123456789UL;
  uint32_t x = (uint32_t)seed;
  uint64_t y = (uint64_t)seed + UINT64_C(0x9e3779b97f4a7c15);
  for (unsigned long i = 0; i < count; ++i) {
    x = x * UINT32_C(1664525) + UINT32_C(1013904223);
    x ^= x >> 13;
    x = (x << 5) | (x >> 27);
    x += UINT32_C(0x7f4a7c15);
    x ^= x << 7;
    x *= UINT32_C(2246822519);
    x ^= x >> 16;
    x -= UINT32_C(0x6a09e667);
    y = y * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407);
    y ^= y >> 29;
    y = (y << 17) | (y >> 47);
    y += UINT64_C(0x94d049bb133111eb);
    y ^= y << 11;
    y *= UINT64_C(0xbf58476d1ce4e5b9);
    y ^= y >> 31;
    y -= UINT64_C(0x243f6a8885a308d3);
  }
  printf("%lu %08x %016lx\n", count, (unsigned int)x, (unsigned long)y);
  return 0;
}

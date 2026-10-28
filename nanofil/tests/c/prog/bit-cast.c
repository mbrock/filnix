/* __builtin_bit_cast(T, E): the bytes of E's value as a T of the same
   size, as through memcpy; immintrin.h's inline functions use it. A
   pointer's bytes keep its address and lose its capability, as memcpy
   to an integer does; an integer cast to a pointer has none. */
#include <stdint.h>
#include <stdio.h>
struct pair { int a, b; };
struct halves { float lo, hi; };
int main(void) {
    float f = 1.5f;
    uint32_t u = __builtin_bit_cast(uint32_t, f);
    double d = __builtin_bit_cast(double, 0x400921fb54442d18ULL);
    struct pair p = { 7, -3 };
    long l = __builtin_bit_cast(long, p);
    struct pair q = __builtin_bit_cast(struct pair, l + 1);
    struct halves h = __builtin_bit_cast(struct halves, 0x3f8000004000000ULL);
    int x = 5;
    int *px = &x;
    uintptr_t a = __builtin_bit_cast(uintptr_t, px);
    int *back = __builtin_bit_cast(int *, a);
    printf("%08x %.6f %lx %d %d %g %g\n", u, d, (unsigned long)l, q.a, q.b,
           h.lo, h.hi);
    printf("%d %d\n", a == (uintptr_t)px, back == px);
    float g = __builtin_bit_cast(float, u + 1) - f;
    printf("%g\n", g * 1e7);
    return 0;
}

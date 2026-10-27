// run: $precision 0
// run: $bits 0
// run: $conversions 0
// run: $unsigned_conversions 0
// run: $comparisons 0
// run: $static_ldouble 0
// run: $calls 3
// run: $choose 1
// run: $choose 0
// run: $variadic 0
// run: $struct_value 0
// run: $nans 0
// long double is x87 80-bit extended, with 64 significand bits: each
// check below fails if it is computed or kept as a double.
static long double third = 1.0L / 3;
static long double table[3] = { 0.1L, -2.5L, 0x1.fffffffffffffffep63L };
static struct { char c; long double v; int after; } holder = { 'h', 1.25L, 77 };

int precision(int unused) {
    long double one = 1.0L, tiny = 0x1p-60L;
    long double sum = one + tiny;
    double d = (double)sum;
    long double prod = 3 * (1.0L / 3);
    return (sum != one) + 2 * (d == 1.0) + 4 * ((sum - one) == tiny)
         + 8 * (prod != 1.0L) + 16 * (sizeof(long double) == 16)
         + 32 * (_Alignof(long double) == 16);
}

int bits(int unused) {
    union { long double v; unsigned char b[16]; } u;
    for (int i = 0; i < 16; i++) u.b[i] = 0xaa;
    u.v = 0.1L;
    // 0.1L is 0x3ffb cccccccccccccccd
    unsigned long mant = 0;
    for (int i = 7; i >= 0; i--) mant = mant << 8 | u.b[i];
    return (mant == 0xcccccccccccccccdUL) + 2 * (u.b[8] == 0xfb) + 4 * (u.b[9] == 0x3f)
         + 8 * (u.b[10] == 0xaa);
}

int conversions(int unused) {
    long double big = 9007199254740993.0L;      // 2^53 + 1, not a double
    long long l = (long long)big;
    float f = (float)third;
    double d = third;
    long double back = d;
    long double neg = -7;
    int i = (int)-2.75L;
    unsigned u = (unsigned)4294967295.0L;
    return (l == 9007199254740993LL) + 2 * (f == 1.0f / 3) + 4 * (d == 1.0 / 3)
         + 8 * (back != third) + 16 * (neg == -7.0) + 32 * (i == -2)
         + 64 * (u == 4294967295U) + 128 * ((long double)1.5f == 1.5L);
}

int unsigned_conversions(int unused) {
    unsigned long max = 18446744073709551615UL;
    long double m = max;                          // exact in 64 bits
    unsigned long back = (unsigned long)m;
    unsigned long half = (unsigned long)0x1p63L;
    unsigned long low = (unsigned long)12345.9L;
    long double from_neg = (long)-1;
    return (back == max) + 2 * (m == 0x1.fffffffffffffffep63L)
         + 4 * (half == 9223372036854775808UL) + 8 * (low == 12345)
         + 16 * (from_neg == -1.0L) + 32 * ((unsigned long)table[2] == max);
}

int comparisons(int unused) {
    long double zero = 0.0L, n = zero / zero, nz = -zero;
    int r = 0;
    if (n == n) r += 1;
    if (n != n) r += 2;
    if (n < 1.0L || n >= 1.0L) r += 4;
    if (nz == zero) r += 8;
    if (1.0L / nz < 0) r += 16;
    if (third > 0.3333333333333333L) r += 32;
    if (!zero) r += 64;
    return r;
}

int static_ldouble(int unused) {
    return (table[0] * 10 > 0.99L) + 2 * (table[1] == -2.5L)
         + 4 * (holder.c == 'h' && holder.v == 1.25L && holder.after == 77)
         + 8 * (third * 3 != 1.0L || third * 3 == 1.0L);
}

static long double scale(long double x, int n) { return x * n; }
static long double pick(int which, long double a, long double b) { return which ? a : b; }
static double narrow(long double x) { return (double)x; }

int calls(int n) {
    long double x = scale(1.0L + 0x1p-62L, n);
    long double y = pick(n, x, -x);
    return (y == 3 + 3 * 0x1p-62L) + 2 * (narrow(y) == 3.0)
         + 4 * (pick(0, 1.0L, 2.0L) == 2.0L);
}

int choose(int c) {
    long double a = 0x1p-63L + 1, b = -4;
    long double r = c ? a : b;
    long double s = (c ?: 2) + 0.5L;
    return (int)(r * 8) + 100 * (r == a) + 1000 * (s == 1.5L);
}

#include <stdarg.h>
static long double vsum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    long double s = 0;
    for (int i = 0; i < n; i++) {
        int k = va_arg(ap, int);
        s += k * va_arg(ap, long double);
    }
    va_end(ap);
    return s;
}

int variadic(int unused) {
    long double r = vsum(3, 1, 0x1p-62L, 2, 1.0L, 3, -0.5L);
    return (r == 0.5L + 0x1p-62L) + 2 * (vsum(0) == 0);
}

struct ld1 { long double v; };
struct ld2 { long double a, b; };
static struct ld1 twice(struct ld1 s) { s.v *= 2; return s; }
static struct ld2 swap(struct ld2 s) { struct ld2 t = { s.b, s.a }; return t; }
static long double vfirst(int n, ...) {
    va_list ap;
    va_start(ap, n);
    struct ld2 s = va_arg(ap, struct ld2);
    struct ld1 t = va_arg(ap, struct ld1);
    va_end(ap);
    return s.a - s.b + t.v;
}

int struct_value(int unused) {
    struct ld1 a = { 1.0L + 0x1p-63L };
    struct ld2 p = { 1.5L, 0x1p-62L };
    struct ld1 b = twice(a);
    struct ld2 q = swap(p);
    return (b.v == 2 + 0x1p-62L) + 2 * (q.a == 0x1p-62L && q.b == 1.5L)
         + 4 * (vfirst(1, p, a) == 1.5L - 0x1p-62L + 1 + 0x1p-63L);
}

// The x87 picks between two NaN operands by quietness, then by the
// larger significand; SSE's rule (the first operand) differs.
static long double nan_bits(unsigned long mant)
{
    union { long double v; unsigned char b[16]; } u = { 0 };
    for (int i = 0; i < 8; i++) u.b[i] = mant >> (8 * i);
    u.b[8] = 0xff; u.b[9] = 0x7f;
    return u.v;
}
static unsigned long low_bits(long double v)
{
    union { long double v; unsigned char b[16]; } u = { v };
    unsigned long r = 0;
    for (int i = 7; i >= 0; i--) r = r << 8 | u.b[i];
    return r;
}
int nans(int unused) {
    long double q1 = nan_bits(0xc000000000000001UL), q2 = nan_bits(0xc000000000000100UL);
    long double s1 = nan_bits(0x8000000000000100UL);
    long double z = 0;
    return (low_bits(q1 + q2) == 0xc000000000000100UL)
         + 2 * (low_bits(q2 * q1) == 0xc000000000000100UL)
         + 4 * (low_bits(s1 - q1) == 0xc000000000000001UL)
         + 8 * (low_bits(z / z) == 0xc000000000000000UL)
         + 16 * (low_bits(-(z / z)) == 0xc000000000000000UL);
}

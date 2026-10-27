// Two unsigned-to-double conversions in a loop: GNU as numeric labels
// repeat within one function.
int two_unsigned_conversions(int n) {
    unsigned long a = 13835058055282163712UL, b = 3;
    double s = 0;
    for (int i = 0; i < n + 2; i++) s += (double)a + (double)b;
    return s == 2 * (0x1.8p63 + 3.0);
}
// run: $mixed 7
// run: $unsigned_conversion 0
// run: $nan_logic 0
// run: $negative_zero 0
// run: $static_float 0
// run: $float_objects 0
// run: $integer_conversions 0
// run: $union_float_bits 0
// run: $union_double_bits 0
// run: $two_unsigned_conversions 0
static double folded = (1.5 + 2) * 0x1.8p+1;
static float rounded = 16777217.0f;
static unsigned int folded_unsigned = (unsigned int)4294967295.0;
static long folded_min = (long)-0x1p63;
static double minus_zero = -0.0;
static int folded_truth = !(-0.0) + 2 * (0.5 && 2.0);
static double selected = 0.0 ? 4 : 2.5f;

int mixed(int x) {
    float f = x + 0.5f;
    double d = f * 2.0;
    f += 0.25;
    ++f;
    return (int)(d + f) + 100 * ((long)(16777216.0f + 1.0) == 16777217L);
}
int unsigned_conversion(int unused) {
    double d = 4294967295.0;
    float f = 0x1p31f;
    double large = 0x1.8p63;
    return (unsigned int)d == 4294967295U
        && (unsigned int)f == 2147483648U
        && (unsigned long)large == 13835058055282163712UL
        && (unsigned char)255.0 == 255;
}
int nan_logic(int unused) {
    double zero = 0.0;
    double n = zero / zero;
    int r = 0;
    if (n == n) r += 1; else r += 2;
    if (n < zero) r += 4; else r += 8;
    if (n <= zero) r += 16; else r += 32;
    if (n > zero) r += 64; else r += 128;
    if (n >= zero) r += 256; else r += 512;
    if (n != n) r += 1024;
    if (!n) r += 2048;
    if (n && 1) r += 4096;
    if (n || 0) r += 8192;
    return r;
}
int negative_zero(int unused) {
    double z = -0.0;
    float f = -0.0f;
    return (1.0 / z < 0.0) + 2 * (1.0f / f < 0.0f)
        + 4 * (1.0 / minus_zero < 0.0) + 8 * (!z && !f);
}
int static_float(int unused) {
    return folded == 10.5 && rounded == 16777216.0
        && folded_unsigned == 4294967295U && folded_truth == 3 && selected == 2.5
        && folded_min == (-9223372036854775807L - 1);
}
int float_objects(int unused) {
    struct { float f[2]; double d; } x = {{1.5f, 2.25f}, 3.5};
    struct { double *p; } holder = {&x.d};
    *holder.p += x.f[0];
    return (int)(x.f[1] + *holder.p) + (int)(unused ? 3 : 1.5);
}
int integer_conversions(int unused) {
    unsigned int u = 4294967295U;
    unsigned long ul = 13835058055282163712UL;
    int i = -123;
    long l = -4294967297L;
    double d = l;
    float f = i;
    return (double)u == 4294967295.0 && (double)ul == 0x1.8p63
        && d == -4294967297.0 && f == -123.0f
        && (long)d == l && (short)f == -123 && (signed char)f == -123
        && (_Bool)-0.0 == 0 && (_Bool)f == 1;
}

// Integer stores followed by float loads must stay in memory under -O.
int union_float_bits(int unused) {
    union { unsigned int i; float f; } x;
    x.i = 1065353216U;
    return x.f == 1.0f;
}
int union_double_bits(int unused) {
    union { unsigned long i; double d; } x;
    x.i = 4607182418800017408UL;
    return x.d == 1.0;
}

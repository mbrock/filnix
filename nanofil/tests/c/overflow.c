// run: $bounds
// run: $mixed
// run: $products
// run: $fixed
// run: $effects

int bounds(void) {
    int i; unsigned u; signed char c; unsigned short h;
    int ok = __builtin_add_overflow(2147483647, 1, &i) && i == (-2147483647-1);
    ok &= !__builtin_add_overflow(2147483647, 0, &i) && i == 2147483647;
    ok &= __builtin_sub_overflow(1u, 2u, &u) && u == 4294967295u;
    ok &= !__builtin_sub_overflow(2u, 1u, &u) && u == 1;
    ok &= __builtin_add_overflow(127, 1, &c) && c == -128;
    ok &= __builtin_sub_overflow(0, 1, &h) && h == 65535;
    return ok;
}
int mixed(void) {
    unsigned u; long l; unsigned long ul;
    int ok = __builtin_add_overflow(-2, 1, &u) && u == 4294967295u;
    ok &= !__builtin_add_overflow(-1, 2u, &u) && u == 1;
    ok &= !__builtin_add_overflow(-1L, 18446744073709551615UL, &ul) && ul == 18446744073709551614UL;
    ok &= __builtin_add_overflow(18446744073709551615UL, 1, &ul) && ul == 0;
    ok &= __builtin_sub_overflow(0UL, 18446744073709551615UL, &l) && l == 1;
    ok &= !__builtin_sub_overflow(9223372036854775808UL, 1, &l) && l == 9223372036854775807L;
    ok &= __builtin_add_overflow(9223372036854775807L, 1UL, &l) && l == (-9223372036854775807L-1);
    return ok;
}
int products(void) {
    long l; unsigned long u; signed char c;
    int ok = __builtin_mul_overflow((-9223372036854775807L-1), -1, &l) && l == (-9223372036854775807L-1);
    ok &= !__builtin_mul_overflow((-9223372036854775807L-1), 1, &l) && l == (-9223372036854775807L-1);
    ok &= !__builtin_mul_overflow((-9223372036854775807L-1), -1, &u) && u == 9223372036854775808UL;
    ok &= __builtin_mul_overflow(-1, 1, &u) && u == 18446744073709551615UL;
    ok &= __builtin_mul_overflow(18446744073709551615UL, 18446744073709551615UL, &u) && u == 1;
    ok &= !__builtin_mul_overflow(4294967295UL, 4294967295UL, &u) && u == 18446744065119617025UL;
    ok &= __builtin_mul_overflow(4294967296UL, 4294967296UL, &u) && u == 0;
    ok &= !__builtin_mul_overflow(-16, 8u, &c) && c == -128;
    ok &= __builtin_mul_overflow(-16, 9u, &c) && c == 112;
    ok &= !__builtin_mul_overflow(18446744073709551615UL, 0, &l) && l == 0;
    return ok;
}
int fixed(void) {
    int i; unsigned u; long l; unsigned long ul; long long ll; unsigned long long ull;
    int ok = __builtin_sadd_overflow(2147483647, 1, &i) && i == (-2147483647-1);
    ok &= __builtin_usub_overflow(0u, 1u, &u) && u == 4294967295u;
    ok &= __builtin_smull_overflow((-9223372036854775807L-1), -1L, &l);
    ok &= __builtin_umull_overflow(18446744073709551615UL, 2UL, &ul) && ul == 18446744073709551614UL;
    ok &= !__builtin_saddll_overflow(-3LL, 2LL, &ll) && ll == -1;
    ok &= __builtin_usubll_overflow(0ULL, 1ULL, &ull) && ull == 18446744073709551615ULL;
    return ok;
}
int effects(void) {
    int a = 1, b = 2, n = 0, r[2];
    int flag = __builtin_add_overflow(a++, b++, &r[n++]);
    return !flag && a == 2 && b == 3 && n == 1 && r[0] == 3
        && sizeof(__builtin_add_overflow(a, b, &r[0])) == sizeof(_Bool);
}

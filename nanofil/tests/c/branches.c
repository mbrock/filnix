// Branch selection (docs/perf.md): a branch on a comparison only it reads
// branches on the flags, in either arm order, with jumps to the next block
// left to fall through. Each condition at w and l, signed and unsigned,
// on both sides of its boundary; a qword constant beyond imm32; a
// comparison also read after the branch, which must stay materialized;
// and arms with phi copies.
int *branches_pointer(int *p) { return p; }

int conditions(int a, int b, unsigned ua, unsigned ub) {
    int r = 0;
    if (a < b) r |= 1;
    if (a <= b) r |= 2;
    if (a > b) r |= 4;
    if (a >= b) r |= 8;
    if (a == b) r |= 16;
    if (a != b) r |= 32;
    if (ua < ub) r |= 64;
    if (ua <= ub) r |= 128;
    if (ua > ub) r |= 256;
    if (ua >= ub) r |= 512;
    return r;
}
long long_conditions(long a, long b, unsigned long ua) {
    long r = 0;
    if (a < b) r |= 1;
    if (a >= b) r |= 2;
    if (ua > 4294967296UL) r |= 4;           // not an imm32
    if (ua < 18446744071562067968UL) r |= 8; // sign-extended imm32
    if (a > -5) r |= 16;
    if (ua <= 2147483647UL) r |= 32;
    return r;
}
// The comparison is read by the branch and by the return.
int reused(int a, int b) {
    int c = a < b;
    if (c) a = a * 3;
    return a + c * 1000;
}
// Phis on both arms, and a loop whose exit test falls through.
int loop(int n, int k) {
    int s = 0, t = 1;
    for (int i = 0; i < n; i++) {
        if (i > k) { s += i; t = t * 3; } else { s -= 1; t = t + 2; }
    }
    return s * 7 + t;
}
// The true arm is the next block; the false edge goes straight to the
// join, whose phi it must still copy (with -O).
int phi_false(int a, int b) {
    int x = 5;
    if (a < b) x = a * 2 + b;
    return x;
}
// run: $phi_false 1 2
// run: $phi_false 2 1
// run: $phi_false 7 7
// run: $conditions 1 2 1 2
// run: $conditions 2 2 2 2
// run: $conditions 3 2 3 2
// run: $conditions 4294967295 1 4294967295 1
// run: $conditions 1 4294967295 1 4294967295
// run: $conditions 2147483648 2147483647 2147483648 2147483647
// run: $long_conditions 1 2 4294967297
// run: $long_conditions 2 2 4294967296
// run: $long_conditions 18446744073709551611 18446744073709551612 18446744071562067967
// run: $long_conditions 18446744073709551612 18446744073709551611 18446744071562067968
// run: $long_conditions 9223372036854775808 9223372036854775807 2147483647
// run: $long_conditions 9223372036854775807 9223372036854775808 2147483648
// run: $reused 1 2
// run: $reused 2 1
// run: $reused 4294967295 0
// run: $loop 10 4
// run: $loop 0 4
// run: $loop 5 9
// run: $loop 7 4294967295

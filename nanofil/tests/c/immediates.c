// Integer immediates are checked against both the interpreter and clang.
// Keep this module in Fil-C mode even after promotion removes all locals.
int *immediate_pointer(int *p) { return p; }

// A 64-bit ALU immediate sign-extends from 32 bits; a 32-bit one may
// carry any bit pattern. Inputs keep these operations unfolded at -O.
unsigned word_immediate(unsigned x, int op) {
    switch (op) {
    case 0: return x + 2147483648u;
    case 1: return x - 4294967295u;
    case 2: return x * 2147483648u;
    case 3: return x & 4294967294u;
    case 4: return x | 2147483648u;
    default: return x ^ 4294967295u;
    }
}
unsigned long long_immediate(unsigned long x, int op) {
    switch (op) {
    case 0: return x + 2147483647UL;
    case 1: return x + 2147483648UL;
    case 2: return x - 18446744071562067968UL;
    case 3: return x & 4294967295UL;
    case 4: return x | 18446744071562067968UL;
    case 5: return x ^ 18446744073709551615UL;
    case 6: return x * 4294967295UL;
    default: return x * 18446744071562067968UL;
    }
}
// run: $word_immediate 2309737967 0
// run: $word_immediate 4294967295 1
// run: $word_immediate 3 2
// run: $word_immediate 2309737967 3
// run: $word_immediate 19088743 4
// run: $word_immediate 2309737967 5
// run: $long_immediate 9223372036854775809 0
// run: $long_immediate 9223372036854775809 1
// run: $long_immediate 9223372036854775809 2
// run: $long_immediate 9223372039164513775 3
// run: $long_immediate 19088743 4
// run: $long_immediate 9223372039164513775 5
// run: $long_immediate 4294967297 6
// run: $long_immediate 4294967297 7

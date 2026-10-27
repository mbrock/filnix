// Switch dispatch (C11 6.8.4.2p5) with enough cases for a binary search:
// the order must be the promoted controlling type's, signed or unsigned,
// at w and at l. Case values are listed out of order on purpose.
// The pointer keeps the module in Fil-C mode, so clang is compared too.
int *switch_pointer(int *p) { return p; }
int signed_int(int x) {
    switch (x) {
    case 7: return 1;
    case -2147483647 - 1: return 2;
    case -1: return 3;
    case 2147483647: return 4;
    case 0: return 5;
    case 100: return 6;
    case -100: return 7;
    case 3: return 8;
    default: return 0;
    }
}
// Signed order would put 0x80000000 and 0xffffffff below 0.
int unsigned_int(unsigned x) {
    switch (x) {
    case 0xffffffffu: return 1;
    case 0x80000000u: return 2;
    case 1: return 3;
    case 0x7fffffffu: return 4;
    case 0: return 5;
    case 0x80000001u: return 6;
    }
    return 0;
}
// A char controls as an int: case values convert to int, not char.
int promoted_char(signed char c) {
    switch (c) {
    case 'a': return 1;
    case -128: return 2;
    case 127: return 3;
    case 0: return 4;
    case -1: return 5;
    case 'z': return 6;
    default: return 7;
    }
}
long signed_long(long x) {
    switch (x) {
    case 4294967296L: return 1;
    case -4294967296L: return 2;
    case 1: return 3;
    case -9223372036854775807L - 1: return 4;
    case 9223372036854775807L: return 5;
    case 0: return 6;
    case 4294967295L: return 7;
    default: return -1;
    }
}
long unsigned_long(unsigned long x) {
    switch (x) {
    case 0xffffffffffffffffUL: return 1;
    case 0x8000000000000000UL: return 2;
    case 0x7fffffffffffffffUL: return 3;
    case 4294967296UL: return 4;
    case 0: return 5;
    case 2: return 6;
    }
    return -1;
}
// Dense, with fallthrough and break, as in a bytecode interpreter.
int dense(int op, int a) {
    switch (op) {
    case 0: a += 1; break;
    case 1: a -= 1; break;
    case 2: a *= 2;
    case 3: a += 3; break;
    case 4: a ^= 5; break;
    case 5: a <<= 1; break;
    case 6: a >>= 1; break;
    case 7: a = -a; break;
    case 8: a = ~a; break;
    case 9: a = a % 7; break;
    case 10: a = a / 3; break;
    case 11: return 11;
    default: a = 1000;
    }
    return a;
}
// run: $signed_int 7
// run: $signed_int 2147483648
// run: $signed_int 4294967295
// run: $signed_int 2147483647
// run: $signed_int 0
// run: $signed_int 100
// run: $signed_int 4294967196
// run: $signed_int 3
// run: $signed_int 4
// run: $signed_int 2147483646
// run: $signed_int 4294967294
// run: $signed_int 101
// run: $unsigned_int 4294967295
// run: $unsigned_int 2147483648
// run: $unsigned_int 1
// run: $unsigned_int 2147483647
// run: $unsigned_int 0
// run: $unsigned_int 2147483649
// run: $unsigned_int 2
// run: $unsigned_int 4294967294
// run: $unsigned_int 2147483650
// run: $promoted_char 97
// run: $promoted_char 128
// run: $promoted_char 127
// run: $promoted_char 0
// run: $promoted_char 255
// run: $promoted_char 122
// run: $promoted_char 98
// run: $promoted_char 129
// run: $signed_long 4294967296
// run: $signed_long 18446744069414584320
// run: $signed_long 1
// run: $signed_long 9223372036854775808
// run: $signed_long 9223372036854775807
// run: $signed_long 0
// run: $signed_long 4294967295
// run: $signed_long 2
// run: $signed_long 18446744073709551615
// run: $signed_long 4294967297
// run: $unsigned_long 18446744073709551615
// run: $unsigned_long 9223372036854775808
// run: $unsigned_long 9223372036854775807
// run: $unsigned_long 4294967296
// run: $unsigned_long 0
// run: $unsigned_long 2
// run: $unsigned_long 1
// run: $unsigned_long 9223372036854775809
// run: $unsigned_long 4294967295
// run: $dense 0 10
// run: $dense 1 10
// run: $dense 2 10
// run: $dense 3 10
// run: $dense 4 10
// run: $dense 5 10
// run: $dense 6 10
// run: $dense 7 10
// run: $dense 8 10
// run: $dense 9 10
// run: $dense 10 10
// run: $dense 11 10
// run: $dense 12 10
// run: $dense 4294967295 10

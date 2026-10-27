/* Operands whose constant value is undefined, in code that never
   evaluates them. Lowering asks whether an arm of ?: is a null pointer
   constant (C11 6.3.2.3p3), which folds it; an undefined value there is
   not a constant (6.5.5p5, 6.5.7p3), not a crash. */
long long cast_quotient(int x) { return x ? (long long)(1 / 0) : 7; }
long long huge_shift(int x) { return x ? (1L << 18446744073709551615u) : 5; }
// run: $cast_quotient 0
// run: $huge_shift 0

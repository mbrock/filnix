// error: static assertion is not a constant
/* C11 6.5.7p3: a shift count of at least the promoted left operand's
   width is undefined, so 1 << 32 is not a constant (6.6p4); clang folds
   it to INT_MIN, and nanofil folded it to 0. */
_Static_assert((1 << 32) == 0, "shift count is the width");

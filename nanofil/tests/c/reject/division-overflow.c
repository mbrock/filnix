// error: static assertion is not a constant
/* C11 6.5.5p6: INT_MIN / -1 is not representable, so the division is
   undefined and not a constant (6.6p4). nanofil folded it to INT_MIN,
   while the IR (and x86 idiv) traps. */
_Static_assert((-2147483647 - 1) / -1 < 0, "quotient overflows");

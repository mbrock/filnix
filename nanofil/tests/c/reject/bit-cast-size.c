// error: __builtin_bit_cast from int to long
long f(int x) { return __builtin_bit_cast(long, x); }

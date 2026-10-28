// error: incrementing or decrementing an _Atomic object is an atomic read-modify-write
_Atomic long hits;
long next(void) { return hits++; }

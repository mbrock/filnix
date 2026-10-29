// error: an asm input tied to an output must have its integer or floating type
/* A tied input of another type would need clang's widening rules. */
int f(long v) { int k; asm("" : "=r"(k) : "0"(v)); return k; }

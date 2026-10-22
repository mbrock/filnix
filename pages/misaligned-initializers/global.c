/* Fil-C: a non-null pointer at a non-word offset in a global initializer. */
int anchor;
struct __attribute__((packed)) P { char c; int *p; };
struct P g = { 1, &anchor };
struct P *expose(void) { return &g; }

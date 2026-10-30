// error: no member named s
/* clang refuses a member of an _Atomic struct (-Watomic-access). */
typedef struct { unsigned s, ns; } t8;
_Atomic(t8) g;
unsigned f(void) { return g.s; }

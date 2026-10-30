// error: _Atomic of a type other than an integer, pointer, float or double
/* An _Atomic struct larger than 8 bytes is lowered by clang to
   libatomic calls, which nanofil does not have. */
typedef struct { int a, b, c; } t12;
_Atomic(t12) g;

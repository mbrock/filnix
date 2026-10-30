// error: a function returning an _Atomic struct or union, or an aggregate holding one, is not supported
/* filcc returns a struct holding an _Atomic struct by its own rules, and
   its code may call a static function whose address escapes. */
typedef struct { char a, b, c; } t3;
typedef struct { _Atomic(t3) v; int k; } W;
static W mk(int k) { W w; w.k = k; return w; }
W (*gr)(int) = mk;

// error: _Atomic of a type other than an integer, pointer, float or double
/* An _Atomic struct holding a pointer would need its capability kept
   through the integer access nanofil makes of it. */
struct p { void *q; };
_Atomic(struct p) g;

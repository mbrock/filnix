// error: _Atomic of a type other than an integer, pointer, float or double
struct pair { int a, b; };
_Atomic(struct pair) shared;

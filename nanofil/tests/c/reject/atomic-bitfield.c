// error: _Atomic bit-field
struct flags { _Atomic unsigned ready : 1; };
int f(void) { struct flags v; return 0; }

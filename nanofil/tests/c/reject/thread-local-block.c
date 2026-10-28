// error: _Thread_local x at block scope must also be static or extern
int f(void) { _Thread_local int x = 1; return x++; }

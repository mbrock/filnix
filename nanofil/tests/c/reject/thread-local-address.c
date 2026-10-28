// error: the address of thread-local t is not a constant
_Thread_local int t;
int *p = &t;

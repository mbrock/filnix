// error: weak thread-local variable tv is not supported
__attribute__((weak)) _Thread_local int tv = 1;
int use(void) { return tv; }

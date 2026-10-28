// error: alignment attributes
int f(void) { _Alignas(32) char line[64]; return line[0]; }

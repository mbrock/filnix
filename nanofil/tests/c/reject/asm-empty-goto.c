// error: asm goto is not supported
int f(int k) { asm goto("" :::: out); return k; out: return 0; }

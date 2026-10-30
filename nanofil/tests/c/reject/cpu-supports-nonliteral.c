// error: __builtin_cpu_supports needs a string literal
int main(void) { const char *f = "avx2"; return __builtin_cpu_supports(f); }

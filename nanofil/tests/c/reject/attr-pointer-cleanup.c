// error: attribute cleanup is not supported in this position
// An attribute among a pointer's qualifiers was dropped: clang runs f.
static void f(char **p) { (void)p; }
int g(void) { char * __attribute__((cleanup(f))) p = 0; return p == 0; }

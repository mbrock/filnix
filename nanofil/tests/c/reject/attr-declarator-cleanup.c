// error: attribute cleanup on one of several declarators is not supported
// It applied to the whole declaration, so f(&a) ran too; clang runs only f(&z).
static void f(int *p) { (void)p; }
int g(void) { int a = 1, z __attribute__((cleanup(f))) = 5; return a + z; }

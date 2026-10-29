// error: attribute constructor on one of several declarators is not supported
// It applied to both functions, so a ran too; clang runs only b.
static void a(void), b(void) __attribute__((constructor));
static void a(void) { }
static void b(void) { }

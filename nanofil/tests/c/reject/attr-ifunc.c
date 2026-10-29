// error: attribute ifunc is not supported
/* Linkage: the symbol resolves at load time. */
static int impl(void) { return 1; }
static int (*resolve(void))(void) { return impl; }
int f(void) __attribute__((ifunc("resolve")));

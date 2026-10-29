// error: attribute weak on one of several declarators is not supported
// It applied to both, so wa was weak too.
extern int wa, wb __attribute__((weak));
int use(void) { return wa; }

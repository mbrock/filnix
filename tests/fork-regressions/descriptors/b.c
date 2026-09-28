__attribute__((noinline)) int which(void) { return 2; }
int callwhich(void) { return which(); }
int (*whichptr(void))(void) { return which; }

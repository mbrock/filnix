// error: alias f of a func names the data x
/* A function alias of an object would hand callers a data object to
   call; nanofil refuses it at compile time (filcc emits it). */
int x;
int f(void) __attribute__((alias("x")));

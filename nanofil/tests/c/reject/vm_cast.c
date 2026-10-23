// error: variably modified types
/* From cproc's vla tests: the cast's size expression has a side effect,
   which nanofil would silently drop. */
int main(void) { int n = 0; (int (*)[++n])0; return n; }

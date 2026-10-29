// error: __auto_type needs one declarator with an expression initializer
/* GCC refuses __auto_type with several declarators. */
int f(void) { __auto_type a = 1, b = 2; return a + b; }

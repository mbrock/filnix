// error: an asm memory operand must have a complete object type
/* clang refuses "+g" on a struct no register holds (a tied indirect
   register input). */
struct S { int a; long b; };
int f(void) { struct S s = {1, 2}; asm volatile("" : "+g"(s)); return s.a; }

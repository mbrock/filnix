// error: whose type may be an aligned typedef
/* clang gives __alignof__ (*p) the typedef's 16; nanofil's types keep
   no typedef and would read int's 4, so it refuses instead. */
typedef int A __attribute__((aligned(16)));
unsigned long f(A *p) { return __alignof__ (*p); }

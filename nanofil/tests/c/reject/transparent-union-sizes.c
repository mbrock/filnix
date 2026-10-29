// error: cannot assign int to union
/* Members of different sizes: clang warns that the transparent_union
   attribute is ignored, and then refuses an int argument for the union
   ("passing 'int' to parameter of incompatible type 'Mixed'"). */
typedef union {
    int i;
    long l;
} __attribute__((__transparent_union__)) Mixed;

long f(Mixed m);

long g(void) { return f(3); }

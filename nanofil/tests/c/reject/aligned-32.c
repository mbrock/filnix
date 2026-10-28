// error: alignment attributes
struct __attribute__((aligned(32))) s { int x; };
struct s v;

// error: alignment attributes
struct __attribute__((packed)) s { char c; int i; };
int f(void) { struct s v; return 0; }

// error: passing a packed
struct __attribute__((packed)) s { char c; int i; };
int f(struct s v) { return v.i; }

// error: more than 16 arguments
struct many { long a[17]; };
long f(struct many m) { return m.a[0]; }
long g(struct many m) { return f(m); }

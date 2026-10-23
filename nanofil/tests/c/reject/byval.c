// error: passing a struct
struct three { long a, b, c; };
long f(struct three t) { return t.a; }

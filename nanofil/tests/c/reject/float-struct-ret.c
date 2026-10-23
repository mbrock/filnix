// error: float-containing struct or union by value
struct large { double d[3]; };
struct large produce(void) { struct large x; return x; }

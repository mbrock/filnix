// error: float-containing struct or union by value
struct outer { union { double d; int i; } inner[2]; };
int consume(struct outer x) { return 0; }

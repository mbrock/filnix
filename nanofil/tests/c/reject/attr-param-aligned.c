// error: attribute aligned is not supported in this position
// A parameter's trailing attributes were dropped.
int g(int x __attribute__((aligned(16)))) { return x; }

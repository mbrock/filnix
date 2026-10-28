/* The objects tests/c/prog/memcpy-small.c shares with clang's side. */
struct holder { char *p; long n; char *q; };
struct holder *lib_make(const char *p, long n, const char *q);
long lib_check(const struct holder *h);

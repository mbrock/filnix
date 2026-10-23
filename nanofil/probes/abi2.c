extern long ext5(long a, char *p, char *q);
long call5(char *p) { return ext5(1, p, p); }
long def5(long a, char *p, char *q) { return a + *p + *q; }
long sum_loop(long *p, long n) { long s = 0; for (long i = 0; i < n; i++) s += p[i]; return s; }
void store_ptr(char **slot, char *v) { *slot = v; }
char *load_ptr(char **slot) { return *slot; }

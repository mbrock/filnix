int counter = 3;
int table[] = {1, 2, 3, 4};
static const char *names[] = {"zero", "one", "two"};
struct pt { int x, y; } origin = { .y = 9 };
int *tp = &table[2];
char buf[8];
static int twice(int x) { return 2 * x; }
static int thrice(int x) { return 3 * x; }
int (*ops[])(int) = { twice, thrice };
int bump(void) { static int n = 10; return n++; }
int name_len(int i) { const char *s = names[i]; int n = 0; while (s[n]) n++; return n; }
int apply(int k, int x) { int (*f)(int) = ops[k]; return f(x) + (*ops[k])(1); }
int globals(int k) { counter += k; buf[3] = 'q'; return counter * 100 + *tp + origin.y + buf[3] + table[3]; }
int bumps(void) { bump(); bump(); return bump(); }
int lit(int i) { return "hello"[i]; }
int poke(void) { char *s = (char *)names[1]; s[0] = 'X'; return s[0]; }
// run: $name_len 0
// run: $name_len 2
// run: $name_len 3
// run: $apply 0 5
// run: $apply 1 5
// run: $apply 2 5
// run: $globals 4
// run: $bumps
// run: $lit 1
// run: $lit 6
// run: $poke
/* Compatible redeclarations (C11 6.2.7p3): the composite keeps what
   either says, an array's size and a prototype; a parameter's own
   qualifiers do not count (6.7.6.3p15). */
int sized[3];
extern int sized[];
int proto(const int x);
int proto();
int proto(int x) { return x + (int)sizeof sized; }
// run: $proto 1

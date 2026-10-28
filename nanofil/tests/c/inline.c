// Callees --inline=small takes (docs/perf.md item 4): static, small,
// called in loops, with locals of each class, a returned local's
// address, void returns, loops of their own; a byval struct and a local
// that only local storage takes (overlapping accesses) stay calls.
struct pair { long x; double y; };
struct big { long a[5]; };

static int clamp(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }
static void bump(int *p, int n) { for (int i = 0; i < n; i++) *p += i; }
static double mix(long a, double b) {
  struct pair p = {a, b};
  double d = p.y * 2;
  long l = p.x + 1;
  return d + l;
}
static int *pick(int c, int *out) {
  int x = 1, y = 2;
  int *p = c ? &x : &y;
  if (&x) *p += 10;
  *out = *p;
  return p;
}
static long bsum(struct big b) { return b.a[0] + b.a[4]; }
static int lo(int v) { union { int i; char c[4]; } u; u.i = v; return u.c[0] + u.c[1]; }
static int first(int *a) { int t[2]; t[0] = a[0]; t[1] = t[0] + 1; return t[1]; }

int clamps(int n) { int s = 0; for (int i = -n; i < n; i++) s += clamp(i * 3, -5, 7); return s; }
int bumps(int n) { int t = 0; for (int i = 0; i < n; i++) bump(&t, i); return t; }
long mixes(int n) { double s = 0; for (int i = 0; i < n; i++) s += mix(i, i * 0.5); return (long)s; }
int picks(void) {
  int u, v;
  unsigned long a = (unsigned long)pick(1, &u), b = (unsigned long)pick(0, &v);
  return u * 100 + v + (a != b) * 1000;
}
long bsums(void) { struct big b = {{1, 2, 3, 4, 5}}; return bsum(b) + bsum(b); }
int firsts(int n) { int a[1] = {n}; int s = 0; for (int i = 0; i < 3; i++) s += first(a); return s; }
int los(int n) { int s = 0; for (int i = 0; i < n; i++) s += lo(i * 300); return s; }
// run: $clamps 4
// run: $clamps 0
// run: $bumps 5
// run: $mixes 4
// run: $picks
// run: $bsums
// run: $firsts 7
// run: $los 5

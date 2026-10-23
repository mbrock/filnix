int add(int a, int b) { return a + b; }
long fact(int n) { long r = 1; while (n > 1) r *= n--; return r; }
int sum(int *p, int n) { int s = 0; for (int i = 0; i < n; i++) s += p[i]; return s; }
int arr(void) { int a[5] = {1, 2, 3}; a[4] = sum(a, 4); return a[4] * 10 + a[3]; }
unsigned char uc(int x) { unsigned char c = x; return c + 1; }
int sw(int x) { switch (x) { case 1: return 10; case 2: case 3: x = 7; break; default: x = -1; } return x; }
int logic(int a, int b) { return (a && b) * 100 + (a || b) * 10 + !a; }
int cond(int a) { return a > 3 ? a * 2 : -a; }
int shifts(int a, unsigned b) { return (a >> 1) + (int)(b >> 1) + (a << 2); }
long ptrs(void) { long x[4] = {5, 6, 7, 8}; long *p = x + 3, *q = &x[1]; return (p - q) * 100 + *p + q[1]; }
int g(void) { int i = 0; again: i++; if (i < 5) goto again; return i; }
int dw(int n) { int c = 0; do { c += n; } while (--n > 0); return c; }
// run: $add 2 3
// run: $add 4294967295 1
// run: $fact 10
// run: $fact 20
// run: $arr
// run: $uc 255
// run: $uc 300
// run: $sw 1
// run: $sw 3
// run: $sw 9
// run: $logic 0 5
// run: $logic 3 5
// run: $cond 5
// run: $cond 2
// run: $shifts 4294967295 4294967295
// run: $shifts 100 7
// run: $ptrs
// run: $g
// run: $dw 4

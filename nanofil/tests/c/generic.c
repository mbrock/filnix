typedef int integer;
typedef const int const_integer;
static int selected = _Generic(123, const int: 1000, unsigned: 2000, int: 32);
int qualified_param(const int *p) {
    return _Generic(p, const int *: 64, int *: 1000, default: 2000);
}
int selection(void) {
    const int x = 7;
    char c = 1;
    char a[4];
    int n = 0;
    int r = _Generic(x, const int: 1000, integer: 1, default: 2000);
    r += _Generic(c, char: 2, int: 4000);
    r += _Generic(a, char *: 4, default: 8000);
    r += _Generic(n++, long: 16000, default: 8);
    _Generic(n, int: n, default: r) = 16;
    const_integer *p = &x;
    r += _Generic(p, const int *: 128, int *: 4000);
    r += _Generic(selection, int (*)(void): 256, default: 8000);
    r += _Generic(1.0f, float: 512, double: 16000);
    return r + n + selected + qualified_param(p);
}
// run: $selection
/* A null pointer constant arm of ?: takes the other arm's pointer type
   (C11 6.5.15p6), also when it is (void *)0 rather than 0. */
long null_arm(long x) {
    int i = 7, *p = &i;
    long r = _Generic(1 ? (void *)0 : p, int *: 1, void *: 1000);
    r += _Generic(x ? p : (void *)(1 - 1), int *: 2, void *: 2000);
    r += _Generic(x ? 0 : p, int *: 4, default: 4000);
    r += _Generic(1 ? (const void *)0 : p, const void *: 8, default: 8000);
    return r + *(x ? p : (void *)0) * 100;
}
// run: $null_arm 1
/* A void * arm that is not a null pointer constant makes ?: a pointer to
   void, qualified with both arms' target qualifiers (C11 6.5.15p6). */
long void_arm(long x) {
    int i = 7, *p = &i;
    void *q = p;
    const void *cq = p;
    long r = _Generic(x ? p : q, void *: 1, int *: 1000);
    r += _Generic(x ? q : p, void *: 2, int *: 2000);
    r += _Generic(x ? (const int *)p : q, const void *: 4, default: 4000);
    r += _Generic(x ? p : cq, const void *: 8, default: 8000);
    return r + *(int *)(x ? p : q) * 100;
}
// run: $void_arm 1
/* The rest of C11 6.5.15p5-6 against clang: arithmetic arms take the
   usual arithmetic conversions, pointer arms the composite type with
   both targets' qualifiers, and (as clang, with a warning) incompatible
   pointer arms void *. Bit i is set when check i selects as clang. */
int (*cond_a3)[3], (*cond_an)[];
int (*cond_f0)(), (*cond_f1)(int);
void cond_void(void) {}
long cond_arms(long x) {
    char c = 1; short sh = 2; unsigned char uc = 3; _Bool b = 1;
    unsigned u = 4; long l = 5; unsigned long ul = 6; float fl = 7; double d = 8;
    int i = 9, *p = &i; long *lp = &l; const int *cp = p; volatile int *vp = p;
    const void *cq = p; void (*fv)(void) = cond_void; int (*f1)(int) = 0;
    long r = 0;
    r |= _Generic(x ? c : c, int: 1, default: 0) << 0;
    r |= _Generic(x ? uc : sh, int: 1, default: 0) << 1;
    r |= _Generic(x ? b : b, int: 1, default: 0) << 2;
    r |= _Generic(x ? u : i, unsigned: 1, default: 0) << 3;
    r |= _Generic(x ? l : u, long: 1, default: 0) << 4;
    r |= _Generic(x ? ul : l, unsigned long: 1, default: 0) << 5;
    r |= _Generic(x ? fl : i, float: 1, default: 0) << 6;
    r |= _Generic(x ? fl : d, double: 1, default: 0) << 7;
    r |= _Generic(x ? p : cp, const int *: 1, default: 0) << 8;
    r |= _Generic(x ? cp : vp, const volatile int *: 1, default: 0) << 9;
    r |= _Generic(x ? cq : vp, const volatile void *: 1, default: 0) << 10;
    r |= _Generic(x ? cond_a3 : cond_an, int (*)[3]: 1, default: 0) << 11;
    r |= _Generic(x ? cond_an : cond_a3, int (*)[3]: 1, default: 0) << 12;
    r |= _Generic(x ? cond_f0 : cond_f1, int (*)(int): 1, default: 0) << 13;
    r |= _Generic(x ? cond_f1 : cond_f0, int (*)(int): 1, default: 0) << 14;
    r |= _Generic(x ? p : lp, void *: 1, default: 0) << 15;
    r |= _Generic(x ? cp : lp, void *: 1, default: 0) << 16;
    r |= _Generic(x ? fv : f1, void *: 1, default: 0) << 17;
    r |= _Generic(x ? 0 : 0L, long: 1, default: 0) << 18;
    x ? (void)0 : i++;
    x ? i++ : (void)0;
    return r + sizeof(*(x ? cond_an : cond_a3)) * 1000000 + i * 100000000;
}
// run: $cond_arms 1
// run: $cond_arms 0

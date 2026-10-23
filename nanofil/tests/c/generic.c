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

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

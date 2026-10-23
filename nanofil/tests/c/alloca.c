int dynamic(int n) {
    unsigned char *p = __builtin_alloca(n);
    p[0] = 17;
    p[n - 1] = 25;
    return p[0] + p[n - 1];
}
int distinct(int n) {
    int *a = __builtin_alloca(n * sizeof(int));
    int *b = __builtin_alloca(n * sizeof(int));
    a[0] = 17;
    b[0] = 25;
    return a[0] + b[0];
}
// run: $dynamic 32
// run: $dynamic 257
// run: $distinct 4

/* Variable length arrays and variably modified types (C11 6.7.6.2):
   storage of the length reached at the declaration, sizeof at run time,
   pointer arithmetic scaled by run-time sizes, bounds checked against
   the actual length, size expressions evaluated once and where C
   evaluates them (declarations, typedefs, casts, sizeof of a VLA type,
   parameters on entry), and not where it does not (sizeof of a pointer
   to one). */
static int calls;
static long count(long x) { calls++; return x; }

long fill(long n) {
    int a[n];
    for (long i = 0; i < n; i++) a[i] = (int)(i * i);
    long s = 0;
    for (long i = 0; i < n; i++) s += a[i];
    return s * 1000 + (long)sizeof a;
}
/* Fil-C allocates at least 16 bytes: with n = 4 the int at index n is
   the first past the object; with n = 8 it is inside. */
long oob(long n) { int a[n]; a[n - 1] = 5; return a[n - 1] + a[4]; }
long below(long n) { char a[n]; char *p = a; return p[-1] + n; }

/* Rows of a run-time width: a[i][j] scales i by m * sizeof(int). */
long matrix(long n) {
    long m = n + 1;
    int a[n][m];
    for (long i = 0; i < n; i++)
        for (long j = 0; j < m; j++) a[i][j] = (int)(i * 10 + j);
    int (*row)[m] = a + 1;
    return a[n - 1][m - 1] * 100000 + (long)sizeof a * 100 + (long)sizeof *row
           + (&a[n - 1] - row) * 1000000000L + (*row)[2] * 10000000L;
}

/* Each size expression is evaluated exactly once, outermost first. */
long once(long n) {
    calls = 0;
    int a[count(n)][count(2)];
    typedef char T[count(n + 1)];
    T t, u;
    long size = (long)sizeof a + (long)sizeof t * 100 + (long)sizeof u * 10000;
    return size * 100 + calls;
}

/* sizeof evaluates its operand only when it is a VLA (6.5.3.4p2). */
long sizes(long n) {
    long c = 0, l = n;
    int (*p)[l] = 0;
    long r = (long)sizeof(c++, p);             /* pointer: not evaluated */
    r = r * 100 + (long)sizeof(*(c++, p));     /* VLA: evaluated */
    r = r * 100 + (long)sizeof(int[++l]);      /* VLA type name */
    r = r * 100 + (long)sizeof(int (*)[++l]);  /* pointer type name: not */
    r = r * 100 + (long)sizeof(int[(c++, 5)]); /* not a constant */
    return r * 100 + c * 10 + l;
}

/* Casts evaluate the sizes of their type names (cproc cast-vm). */
long casts(long n) {
    long l = 0;
    int a[n];
    a[n - 1] = 7;
    int (*p)[n] = &a;
    long k = ((long (*)[++l])(void *)p == 0) + ((int (*)[++l])p)[0][n - 1];
    return k * 10 + l;
}

/* A parameter's size expression uses an earlier parameter. */
static long rows(long n, long m, int a[n][m]) {
    long s = 0;
    for (long i = 0; i < n; i++) s += a[i][m - 1];
    return s * 1000 + (long)sizeof *a;
}
long params(long n) {
    int a[n][3];
    for (long i = 0; i < n; i++) a[i][2] = (int)i + 1;
    return rows(n, 3, a);
}

/* A loop allocates a fresh array each iteration; jumps backward within
   the scope are allowed (c-testsuite 00207). */
long loop(long n) {
    long t = 0;
    for (long i = 1; i <= n; i++) { char b[i]; b[i - 1] = (char)i; t += b[i - 1] + (long)sizeof b; }
    long k = n;
    { char x[k]; again: x[0] = 1; if (k-- > 1) goto again; t += x[0]; }
    return t;
}
/* A static pointer to a VLA is allowed; its size expression is evaluated
   where the declaration is reached (cproc's C23 constraint test). */
static long gx;
long static_vm(long n) { static int (*a)[gx = n]; int b[3]; a = &b; return gx * 100 + (long)sizeof *a; }
// run: $fill 5
// run: $fill 1
// run: $oob 8
// run: $oob 4
// run: $below 3
// run: $matrix 3
// run: $once 3
// run: $sizes 2
// run: $casts 4
// run: $params 4
// run: $loop 4
// run: $static_vm 3

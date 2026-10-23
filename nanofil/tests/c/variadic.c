// run: $variadic_test 0
// run: $variadic_test 1
// run: $variadic_overrun
// run: $variadic_fixed_pointers
// run: $variadic_bad_pointer
// run: $variadic_struct_return
#include <stdarg.h>

static long consume(va_list *ap) { return va_arg(*ap, long); }
static long clobber(int n, ...) { return n; }

static long mixed(int mixed, ...) {
    va_list ap, copy;
    clobber(99, 1, 2, 3, 4, 5);
    va_start(ap, mixed);
    int i = va_arg(ap, int);
    va_copy(copy, ap);
    long l = consume(&ap);
    long again = va_arg(copy, long);
    int *p = va_arg(ap, int *);
    va_end(copy);
    va_end(ap);
    va_start(ap, mixed);
    int first = va_arg(ap, int);
    va_end(ap);
    return i + l + again + *p + first;
}

long variadic_test(int n) {
    int value = 7 + n;
    return mixed(3, 11, 10000000000L, &value);
}

static long overrun(int n, ...) {
    va_list ap;
    va_start(ap, n);
    long a = va_arg(ap, long);
    long b = va_arg(ap, long);
    va_end(ap);
    return a + b;
}

long variadic_overrun(void) { return overrun(1, 42L); }

/* Fixed pointers and the hidden snapshot cross the register/stack split. */
static long fixed(int *a, long b, int *c, long d, int *e, ...) {
    va_list ap;
    va_start(ap, e);
    long x = va_arg(ap, long);
    va_end(ap);
    return *a + b + *c + d + *e + x;
}
long variadic_fixed_pointers(void) {
    int n = 7;
    long (*fp)(int *, long, int *, long, int *, ...) = fixed;
    return fp(&n, 11L, &n, 13L, &n, 10000000000L);
}

static int bad_pointer(int n, ...) {
    va_list ap;
    va_start(ap, n);
    int *p = va_arg(ap, int *);
    va_end(ap);
    return *p;
}
long variadic_bad_pointer(void) { return bad_pointer(1, 123L); }

struct pair { int *p; long n; };
static struct pair make_pair(int n, ...) {
    va_list ap;
    va_start(ap, n);
    struct pair r;
    r.p = va_arg(ap, int *);
    r.n = va_arg(ap, long);
    va_end(ap);
    return r;
}
long variadic_struct_return(void) {
    int n = 7;
    struct pair r = make_pair(2, &n, 10000000000L);
    return *r.p + r.n;
}

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

long nsum(int n, ...);
long ncall(int *p);
long nconsume(va_list ap);
long nforward(int n, ...);
int *nptr(int n, ...);
long ntrap(int n, ...);

void churn(void) {
    zgc_request_and_wait();
}

long csum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    int i = va_arg(ap, int);
    long l = va_arg(ap, long);
    int *p = va_arg(ap, int *);
    va_end(ap);
    return i + l + *p;
}
long cconsume(va_list ap) { return va_arg(ap, long); }
static long call_consume(int n, ...) {
    va_list ap;
    va_start(ap, n);
    long v = nconsume(ap);
    va_end(ap);
    return v;
}

int main(int argc, char **argv) {
    int *p = malloc(sizeof(int));
    *p = 7;
    switch (atoi(argv[1])) {
    case 0: printf("%ld\n", nsum(3, 11, 10000000000L, p)); break;
    case 1: printf("%ld\n", ncall(p)); break;
    case 2: printf("%ld\n", call_consume(1, 12345678901L)); break;
    case 3: printf("%ld\n", nforward(1, 12345678901L)); break;
    case 4: printf("%d\n", *nptr(1, p)); break;
    case 5: printf("%ld\n", ntrap(1, 42L)); break;
    case 6: printf("%ld\n", ((long (*)(int, ...))nsum)(3, 11, 10000000000L, p)); break;
    }
    return 0;
}

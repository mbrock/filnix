// args: 32
#include <stdlib.h>
int main(int argc, char **argv) {
    unsigned long n = strtoul(argv[1], 0, 10);
    volatile char *p = __builtin_alloca(n);
    p[n - 1] = 42;
    p[n] = 17;
    return 0;
}

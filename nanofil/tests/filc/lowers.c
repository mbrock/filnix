#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

long dead_root(void);
long redefined_root(void);

/* Two objects told apart by value: the flight reads c_pair's second word. */
void *c_pair(void)
{
    long *p = malloc(2 * sizeof(*p));
    p[0] = 73;
    p[1] = 11;
    return p;
}

void *c_other(void)
{
    long *p = malloc(sizeof(*p));
    *p = 100;
    return p;
}

void c_collect(void)
{
    zgc_request_and_wait();
    zgc_request_and_wait();
}

int main(int argc, char **argv)
{
    switch (atoi(argv[1])) {
    case 0: printf("dead root = %ld\n", dead_root()); break;
    case 1: printf("redefined root = %ld\n", redefined_root()); break;
    }
    return 0;
}

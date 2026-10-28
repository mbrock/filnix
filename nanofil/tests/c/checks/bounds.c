/* The access-check boundaries of docs/perf.md item 6a, one per run:
   bounds CASE SIZE OP, with SIZE one of 1, 2, 4, 8 and 10 (a long
   double) and OP read or write. tests/checks.sh compares each run under
   -O (no borrow test) with -O --registers=stack (the reference). The
   object is 16 bytes, so upper - SIZE is the last legal start. A long
   double must be 8-aligned and objects are 16-byte multiples, so
   upper - 10 is never a legal start: its object is 32 bytes, its last
   start upper - 16 and its straddling start upper - 8. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ACCESS(T, P)                                     \
    do {                                                 \
        if (write) *(T *)(P) = (T)7;                     \
        else printf("%d\n", (int)*(T *)(P));             \
    } while (0)

static void access(char *p, int size, int write)
{
    switch (size) {
    case 1: ACCESS(signed char, p); break;
    case 2: ACCESS(short, p); break;
    case 4: ACCESS(int, p); break;
    case 8: ACCESS(long, p); break;
    default: ACCESS(long double, p); break;
    }
}

int main(int argc, char **argv)
{
    if (argc < 4) return 2;
    const char *c = argv[1];
    int size = atoi(argv[2]);
    int write = !strcmp(argv[3], "write");
    int n = size == 10 ? 32 : 16;
    int last = size == 10 ? 16 : size, over = size == 10 ? 8 : size - 1;
    char *o = malloc(n);
    memset(o, 1, n);
    char *p;
    if (!strcmp(c, "lower")) p = o;                           /* passes */
    else if (!strcmp(c, "last")) p = o + n - last;            /* passes */
    else if (!strcmp(c, "straddle")) p = o + n - over;        /* traps */
    else if (!strcmp(c, "end")) p = o + n;                    /* traps */
    else if (!strcmp(c, "below")) p = o - 1;                /* traps */
    else if (!strcmp(c, "freed")) { free(o); p = o; }       /* traps */
    else if (!strcmp(c, "null")) p = 0;                     /* traps */
    else return 2;
    access(p, size, write);
    printf("ok\n");
    return 0;
}

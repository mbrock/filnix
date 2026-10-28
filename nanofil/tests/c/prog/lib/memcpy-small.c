/* clang's side of tests/c/prog/memcpy-small.c: holders of pointers made
   and dereferenced by clang-built code. */
#include <stdlib.h>
#include <string.h>
#include "memcpy-small.h"

struct holder *lib_make(const char *p, long n, const char *q)
{
    struct holder *h = malloc(sizeof *h);
    h->p = strdup(p);
    h->n = n;
    h->q = strdup(q);
    return h;
}

long lib_check(const struct holder *h)
{
    return (long)strlen(h->p) * 1000 + h->n * 10 + (long)strlen(h->q);
}

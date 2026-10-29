// GNU C: sizeof a function type or void is 1. curl's typecheck-gcc.h
// (in git's imap-send.c and tpm2-tss) checks a callback with
// sizeof(expr) == sizeof(void *) on a function designator.
#include <stdio.h>

static size_t callback(char *p, size_t n, size_t m, void *u) {
    (void)p; (void)u;
    return n * m;
}

typedef int fn(void);

#define any_ptr(expr) (sizeof(expr) == sizeof(void *))

static const unsigned long folded[] = {sizeof(callback), sizeof(fn), sizeof(void),
                                       sizeof(const void)};

int main(void) {
    printf("%zu %zu %zu %d %d\n", sizeof callback, sizeof(fn), sizeof(void),
           any_ptr(callback), any_ptr(&callback));
    printf("%lu %lu %lu %lu %zu\n", folded[0], folded[1], folded[2], folded[3],
           callback(0, 2, 3, 0));
    return 0;
}

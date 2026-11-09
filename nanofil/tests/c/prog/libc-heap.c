// cflags: -D_GNU_SOURCE -fno-builtin
// Reallocation is not an in-place write contract: the old aliases may
// die. Overflow refusal is distinct from a successful zero-size object.
#include <errno.h>
#include <stdint.h>
#include "libc-probe.h"
static void interior_free(void) { char *p = malloc(8); free(p + 1); }
static void double_free(void) { char *p = malloc(8); free(p); free(p); }
static void realloc_alias(void) {
    char *p = malloc(16);
    p[0] = 7;
    char *q = realloc(p, 32);
    if (!q) _exit(0);
    volatile char c = p[0];
    (void)c;
}
int main(void) {
    free(0);
    char *kept = "authority";
    unsigned char *fresh = malloc(17), *other = malloc(17);
    int fresh_ok = fresh && other && fresh != other &&
        (uintptr_t)fresh % 16 == 0 && (uintptr_t)other % 16 == 0;
    for (unsigned i = 0; i < 17; ++i) fresh_ok = fresh_ok && fresh[i] == 0 && other[i] == 0;
    fresh[0] = 41; fresh[16] = 97;
    answer("malloc fresh aligned storage frames old objects", fresh_ok && other[0] == 0 && other[16] == 0 && kept[2] == 't');
    void *empty = malloc(0);
    answer("malloc zero returns freeable nonnull storage", empty != 0 && (uintptr_t)empty % 16 == 0);
    free(empty); free(fresh); free(other);
    unsigned char *p = calloc(3, 7);
    int zero = p != 0;
    for (int i = 0; i < 21; ++i) if (p[i]) zero = 0;
    answer("calloc product is zeroed", zero);
    p[0] = 17; p[20] = 93;
    unsigned char *q = realloc(p, 29);
    answer("realloc preserves old prefix", q && q[0] == 17 && q[20] == 93);
    unsigned char *r = reallocarray(q, 2, 5);
    answer("reallocarray shrink preserves prefix", r && r[0] == 17);
    volatile size_t huge = SIZE_MAX;
    errno = 0;
    void *refused = reallocarray(r, huge, 2);
    answer("overflow refusal keeps old allocation", !refused && errno == ENOMEM && r[0] == 17);
    errno = 0;
    answer("calloc overflow refuses", !calloc(huge, 2) && errno == ENOMEM);
    free(r);
    p = realloc(0, 7);
    answer("realloc null allocates", p != 0);
    free(p);
    answer("free needs allocation base", libc_traps(interior_free));
    answer("free consumes lifetime", libc_traps(double_free));
    answer("successful realloc ends old aliases", libc_traps(realloc_alias));
    return 0;
}

/* The failing small copies of docs/perf.md item 7a, one per run:
   traps CASE N, with N one of 1, 8, 9, 16. tests/memcpy.sh compares
   each run under -O (the inline filter) with -O --memcpy=call. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

struct holder { char *p; long n; };

static char *src16(void)
{
    char *s = malloc(16);
    memcpy(s, "0123456789abcdef", 16);
    return s;
}

#define COPY(D, S) switch (n) {          \
    case 1: memcpy(D, S, 1); break;      \
    case 8: memcpy(D, S, 8); break;      \
    case 9: memcpy(D, S, 9); break;      \
    default: memcpy(D, S, 16); break; }

int main(int argc, char **argv)
{
    if (argc < 3) return 2;
    const char *c = argv[1];
    int n = atoi(argv[2]);
    char *s = src16();
    char *d = malloc(16);
    if (!strcmp(c, "dst-aux")) {
        /* Overwrites a held pointer's bytes: the runtime clears its
           capability, so the dereference after it traps. */
        struct holder *h = malloc(2 * sizeof *h);
        h[0].p = s; h[1].p = s;
        /* The same bytes as integers, so the source has no aux. */
        long *bytes = malloc(2 * sizeof *bytes);
        bytes[0] = (long)(uintptr_t)s; bytes[1] = 0;
        COPY((char *)h, (char *)bytes);
        printf("%c\n", *h[0].p);
    } else if (!strcmp(c, "src-aux")) {
        /* Copies a pointer's bytes into plain memory: the runtime gives
           the destination aux and the copied capability. */
        struct holder *h = malloc(2 * sizeof *h);
        h[0].p = s; h[0].n = 0; h[1].p = s; h[1].n = 0;
        struct holder *e = malloc(2 * sizeof *e);
        memset(e, 0, 2 * sizeof *e);
        COPY((char *)e, (char *)h);
        printf("%c\n", n >= 8 ? *e[0].p : 'x');
        if (n < 8) *e[0].p = 0;
    } else if (!strcmp(c, "readonly")) {
        COPY((char *)"a read-only string literal", s);
    } else if (!strcmp(c, "freed-dst")) {
        free(d); COPY(d, s);
    } else if (!strcmp(c, "freed-src")) {
        free(s); COPY(d, s);
    } else if (!strcmp(c, "dst-end")) {
        char *m = malloc(n); COPY(m + 1, s);
    } else if (!strcmp(c, "dst-below")) {
        COPY(d - 1, s);
    } else if (!strcmp(c, "src-end")) {
        char *m = malloc(n); memset(m, 1, n); COPY(d, m + 1);
    } else if (!strcmp(c, "src-below")) {
        COPY(d, s - 1);
    } else if (!strcmp(c, "null-dst")) {
        /* Through a volatile integer, which clang cannot fold back. */
        volatile uintptr_t u = (uintptr_t)d;
        COPY((char *)u, s);
    } else if (!strcmp(c, "null-src")) {
        volatile uintptr_t u = (uintptr_t)s;
        COPY(d, (char *)u);
    } else if (!strcmp(c, "function")) {
        COPY(d, (char *)main);
    } else if (!strcmp(c, "empty")) {
        COPY((char *)malloc(0), s);
    } else if (!strcmp(c, "result")) {
        char *m = malloc(n);
        char *r = memcpy(m, s, 1);
        r[n] = 0;
    } else return 2;
    printf("survived %s %d\n", c, n);
    return 0;
}

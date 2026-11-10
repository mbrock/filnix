/* Compare the functions rx.pl made (rx_NAME in the shared object argv[1])
   with PCRE2's interpreter on the patterns and subject of
   ../pcre2-sljit-llvm/pats.h: from every start offset of the subject the
   two must agree on the result and on the whole ovector. Then time the
   find-all loop with both.
   The patterns of more.h are only checked.

   bench RX.so [seconds] [pattern] */
#define PCRE2_CODE_UNIT_WIDTH 8
#include <dlfcn.h>
#include <pcre2.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

#include "pats.h"

#include "more.h"

typedef int rx_fn(const char *subject, long length, long start, long *ovector, long *stack, long slimit,
                  long budget);

#define STACK 65536
#define BUDGET 10000000 /* PCRE2's default match limit */
static long stack[STACK];

struct run {
    unsigned long calls, matches, sum;
    double ns;
};

/* One find-all pass over the subject with either matcher. */
static void pass(pcre2_code *re, pcre2_match_data *md, rx_fn *rx, const char *subj, size_t len, struct run *r)
{
    PCRE2_SIZE *ov = pcre2_get_ovector_pointer(md);
    size_t off = 0;
    for (;;) {
        int rc = rx ? rx(subj, len, off, (long *)ov, stack, STACK, BUDGET)
                    : pcre2_match(re, (PCRE2_SPTR)subj, len, off, 0, md, NULL);
        r->calls++;
        if (rc <= 0) {
            if (rx && rc < 0) {
                printf("rx gave up: %d\n", rc);
                exit(1);
            }
            break;
        }
        r->matches++;
        r->sum += ov[0] * 31 + ov[1];
        off = ov[1] > ov[0] ? ov[1] : ov[1] + 1;
        if (off > len)
            break;
    }
}

static void timed(pcre2_code *re, pcre2_match_data *md, rx_fn *rx, const char *subj, size_t len, double budget,
                  struct run *r)
{
    unsigned long passes = 0;
    double t0 = now(), t1;
    memset(r, 0, sizeof *r);
    do {
        for (int it = 0; it < 20; it++, passes++)
            pass(re, md, rx, subj, len, r);
        t1 = now();
    } while (t1 - t0 < budget);
    r->ns = (t1 - t0) * 1e9 / r->calls;
    r->calls /= passes, r->matches /= passes, r->sum /= passes;
}

/* Both matchers from every start offset of the subject: the number of
   calls that disagree, and how many calls and matches there were. */
static unsigned long differences(pcre2_code *re, rx_fn *rx, const char *subj, size_t len, unsigned long *calls,
                                 unsigned long *matches)
{
    uint32_t groups;
    pcre2_pattern_info(re, PCRE2_INFO_CAPTURECOUNT, &groups);
    pcre2_match_data *md = pcre2_match_data_create_from_pattern(re, NULL);
    PCRE2_SIZE *ov = pcre2_get_ovector_pointer(md);
    long *mine = malloc(sizeof(long) * 2 * (groups + 1));
    unsigned long bad = 0;
    for (size_t off = 0; off <= len; off++) {
        int rc = pcre2_match(re, (PCRE2_SPTR)subj, len, off, 0, md, NULL);
        int rc2 = rx(subj, len, off, mine, stack, STACK, BUDGET);
        ++*calls;
        *matches += rc > 0;
        if ((rc > 0) != (rc2 > 0) || (rc > 0 && memcmp(ov, mine, sizeof(long) * 2 * (groups + 1)))) {
            if (!bad++) {
                printf("  at %zu: pcre2 %d, rx %d\n", off, rc, rc2);
                for (uint32_t g = 0; rc > 0 && rc2 > 0 && g <= groups; g++)
                    printf("  group %u: pcre2 %ld..%ld, rx %ld..%ld\n", g, (long)ov[2 * g], (long)ov[2 * g + 1],
                           mine[2 * g], mine[2 * g + 1]);
            }
        }
    }
    pcre2_match_data_free(md);
    free(mine);
    return bad;
}

int main(int argc, char **argv)
{
    double budget = argc > 2 ? atof(argv[2]) : 0.3;
    size_t reps = 8, hl = sizeof(html) - 1;
    char *big = malloc(hl * reps + 1);
    for (size_t i = 0; i < reps; i++)
        memcpy(big + i * hl, html, hl);
    big[hl * reps] = 0;
    void *so = dlopen(argv[1], RTLD_NOW);
    if (!so) {
        fprintf(stderr, "%s\n", dlerror());
        return 1;
    }
    int status = 0;
    size_t timed_pats = sizeof(pats) / sizeof(pats[0]), all = timed_pats + sizeof(more) / sizeof(more[0]);
    printf("%-10s %6s %10s %10s %7s\n", "pattern", "calls", "pcre2 ns", "rx ns", "speedup");
    for (size_t p = 0; p < all; p++) {
        const struct pat *pat = p < timed_pats ? &pats[p] : &more[p - timed_pats];
        int err;
        PCRE2_SIZE eo;
        char name[64];
        if (argc > 3 && strcmp(argv[3], pat->name))
            continue;
        snprintf(name, sizeof name, "rx_%s", pat->name);
        rx_fn *rx = (rx_fn *)dlsym(so, name);
        if (!rx) {
            printf("%-10s not compiled\n", pat->name);
            continue;
        }
        pcre2_code *re = pcre2_compile((PCRE2_SPTR)pat->re, PCRE2_ZERO_TERMINATED, pat->opts, &err, &eo, NULL);
        const char *subj = pat->subject ? pat->subject : big;
        size_t len = strlen(subj);
        unsigned long n = 0, m = 0, bad = differences(re, rx, subj, len, &n, &m);
        if (bad) {
            printf("%-10s %lu of %lu calls differ\n", pat->name, bad, n);
            status = 1;
            continue;
        }
        if (p >= timed_pats) {
            printf("%-10s agrees on %lu calls, %lu of them matches\n", pat->name, n, m);
            pcre2_code_free(re);
            continue;
        }
        pcre2_match_data *md = pcre2_match_data_create_from_pattern(re, NULL);
        struct run a, b;
        timed(re, md, NULL, subj, len, budget, &a);
        timed(re, md, rx, subj, len, budget, &b);
        if (a.calls != b.calls || a.sum != b.sum)
            status = 1;
        printf("%-10s %6lu %10.1f %10.1f %6.1fx\n", pat->name, a.calls, a.ns, b.ns, a.ns / b.ns);
        pcre2_match_data_free(md);
        pcre2_code_free(re);
    }
    return status;
}

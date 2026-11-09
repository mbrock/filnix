/* Regex throughput harness: for each pattern, find all matches in a subject,
   repeat, and report ns per pcre2_match call.  With argv[1] == "jit" the
   pattern is JIT compiled first (and the JIT compile time is reported). */
#define PCRE2_CODE_UNIT_WIDTH 8
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

int main(int argc, char **argv)
{
    int use_jit = argc > 1 && !strcmp(argv[1], "jit");
    double budget = argc > 2 ? atof(argv[2]) : 0.5;
    size_t reps = 8, hl = sizeof(html) - 1;
    char *big = malloc(hl * reps + 1);
    for (size_t i = 0; i < reps; i++)
        memcpy(big + i * hl, html, hl);
    big[hl * reps] = 0;

    for (size_t p = 0; p < sizeof(pats) / sizeof(pats[0]); p++) {
        int err;
        if (argc > 3 && strcmp(argv[3], pats[p].name))
            continue;
        PCRE2_SIZE eo;
        pcre2_code *re = pcre2_compile((PCRE2_SPTR)pats[p].re, PCRE2_ZERO_TERMINATED, pats[p].opts, &err, &eo, NULL);
        if (!re) {
            printf("%s: compile error %d\n", pats[p].name, err);
            continue;
        }
        double jit_ms = 0;
        if (use_jit) {
            double t = now();
            int rc = pcre2_jit_compile(re, PCRE2_JIT_COMPLETE);
            jit_ms = (now() - t) * 1e3;
            if (rc) {
                printf("%s: jit compile failed %d\n", pats[p].name, rc);
                continue;
            }
        }
        const char *subj = pats[p].subject ? pats[p].subject : big;
        size_t len = strlen(subj);
        pcre2_match_data *md = pcre2_match_data_create_from_pattern(re, NULL);
        unsigned long calls = 0, matches = 0, sum = 0, passes = 0;
        double t0 = now(), t1;
        do {
            for (int it = 0; it < 20; it++) {
                size_t off = 0;
                passes++;
                for (;;) {
                    int rc = pcre2_match(re, (PCRE2_SPTR)subj, len, off, 0, md, NULL);
                    calls++;
                    if (rc < 0)
                        break;
                    PCRE2_SIZE *ov = pcre2_get_ovector_pointer(md);
                    matches++;
                    sum += ov[0] * 31 + ov[1];
                    off = ov[1] > ov[0] ? ov[1] : ov[1] + 1;
                    if (off > len)
                        break;
                }
            }
            t1 = now();
        } while (t1 - t0 < budget);
        printf("%-10s len=%-5zu calls/pass=%-5lu ns/call=%-9.1f us/pass=%-9.2f sum=%lu", pats[p].name, len,
               calls / passes, (t1 - t0) * 1e9 / calls, (t1 - t0) * 1e6 / passes, sum / passes);
        if (use_jit)
            printf(" jit_compile_ms=%.3f", jit_ms);
        printf("\n");
        pcre2_match_data_free(md);
        pcre2_code_free(re);
    }
    return 0;
}

/* Check a libpcre2 that has the hook (pcre2-rx-hook.patch) against its
   own interpreter, through the public API only. Each pattern of
   ../pcre2-sljit-llvm/pats.h and more.h is compiled twice and one copy
   is given to pcre2_jit_compile. From every start offset of the subject
   the two must then agree on the return value, the ovector and the
   start character: with ovectors of several sizes, with match options
   and limits the compiled function does not handle or runs into, through
   pcre2_jit_match, and through pcre2_substitute. Then time the find-all
   loop of pats.h's patterns with both. Last, compile the first pattern
   20 times again, as a program does that compiles its patterns per
   request, and check that none of those compiles maps code.

   PCRE2_RX_CACHE and PCRE2_RX_COMPILER must be set as pcre2_rx_inc.h
   says. The `ms` column is the time pcre2_jit_compile took: with an
   empty cache the compiler ran, with a full one the shared object was
   loaded.

   hook [seconds] [pattern] */
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

#include "more.h"

/* Loops over a group that push on the backtrack stack once per
   iteration, so that it has to grow, and the same with captures; and
   one that backtracks until the pattern's own match limit stops it. */
static const struct pat hard[] = {
    { "deep", "^(?:a|ab)*!", 0, NULL },
    { "deep2", "(?:(a)|(b))*!(c)?", 0, NULL },
    { "limit", "(*LIMIT_MATCH=20000)^(a+)*\\d", 0, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" },
};

enum how { MATCH, JIT_MATCH };

static int match(enum how how, pcre2_code *re, const char *subj, size_t len, size_t off, uint32_t options,
                 pcre2_match_data *md, pcre2_match_context *mc)
{
    return how == JIT_MATCH ? pcre2_jit_match(re, (PCRE2_SPTR)subj, len, off, options, md, mc)
                            : pcre2_match(re, (PCRE2_SPTR)subj, len, off, options, md, mc);
}

/* The compiled pattern `rx` and the interpreted one `in` from every
   start offset, with an ovector of `pairs` pairs: the number of calls
   that differ. */
static unsigned long differences(const char *what, enum how how, pcre2_code *rx, pcre2_code *in, uint32_t groups,
                                 uint32_t pairs, uint32_t options, pcre2_match_context *mc, const char *subj,
                                 size_t len, size_t step, unsigned long *calls)
{
    pcre2_match_data *a = pcre2_match_data_create(pairs, NULL), *b = pcre2_match_data_create(pairs, NULL);
    PCRE2_SIZE *ova = pcre2_get_ovector_pointer(a), *ovb = pcre2_get_ovector_pointer(b);
    uint32_t set = pairs < groups + 1 ? pairs : groups + 1;
    unsigned long bad = 0;
    for (size_t off = 0; off <= len; off += step) {
        int rca = match(how, rx, subj, len, off, options, a, mc);
        int rcb = match(MATCH, in, subj, len, off, options, b, mc);
        PCRE2_SIZE la = 0, lb = 0;
        int same = rca == rcb;
        if (same && rca >= 0) {
            same = !memcmp(ova, ovb, sizeof(PCRE2_SIZE) * 2 * set) && pcre2_get_startchar(a) == pcre2_get_startchar(b);
            /* The subject the match data remembers, or its copy. */
            same = same && pcre2_substring_length_bynumber(a, 0, &la) == pcre2_substring_length_bynumber(b, 0, &lb) &&
                   la == lb;
        }
        ++*calls;
        if (!same && !bad++) {
            printf("  %s, %u pairs, at %zu: rx %d, interpreter %d\n", what, pairs, off, rca, rcb);
            for (uint32_t g = 0; rca >= 0 && rcb >= 0 && g < set; g++)
                printf("  group %u: rx %ld..%ld, interpreter %ld..%ld\n", g, (long)ova[2 * g], (long)ova[2 * g + 1],
                       (long)ovb[2 * g], (long)ovb[2 * g + 1]);
        }
    }
    pcre2_match_data_free(a);
    pcre2_match_data_free(b);
    return bad;
}

/* pcre2_substitute, which matches repeatedly with its own match data and
   options: 1 when the two differ. */
static unsigned long substitute_differs(pcre2_code *rx, pcre2_code *in, const char *subj, size_t len)
{
    PCRE2_SIZE la = 4 * len + 64, lb = la;
    PCRE2_UCHAR *a = malloc(la), *b = malloc(lb);
    int rca = pcre2_substitute(rx, (PCRE2_SPTR)subj, len, 0, PCRE2_SUBSTITUTE_GLOBAL, NULL, NULL, (PCRE2_SPTR) "[$0]", 4,
                               a, &la);
    int rcb = pcre2_substitute(in, (PCRE2_SPTR)subj, len, 0, PCRE2_SUBSTITUTE_GLOBAL, NULL, NULL, (PCRE2_SPTR) "[$0]", 4,
                               b, &lb);
    int differs = rca != rcb || (rca >= 0 && (la != lb || memcmp(a, b, la)));
    if (differs)
        printf("  substitute: rx %d, interpreter %d\n", rca, rcb);
    free(a);
    free(b);
    return differs;
}

struct run {
    unsigned long calls, sum;
    double ns;
};

/* One find-all pass over the subject. */
static void pass(enum how how, pcre2_code *re, pcre2_match_data *md, const char *subj, size_t len, struct run *r)
{
    PCRE2_SIZE *ov = pcre2_get_ovector_pointer(md);
    size_t off = 0;
    for (;;) {
        int rc = match(how, re, subj, len, off, 0, md, NULL);
        r->calls++;
        if (rc <= 0)
            break;
        r->sum += ov[0] * 31 + ov[1];
        off = ov[1] > ov[0] ? ov[1] : ov[1] + 1;
        if (off > len)
            break;
    }
}

static void timed(enum how how, pcre2_code *re, const char *subj, size_t len, double budget, struct run *r)
{
    pcre2_match_data *md = pcre2_match_data_create_from_pattern(re, NULL);
    unsigned long passes = 0;
    double t0 = now(), t1;
    memset(r, 0, sizeof *r);
    do {
        for (int it = 0; it < 20; it++, passes++)
            pass(how, re, md, subj, len, r);
        t1 = now();
    } while (t1 - t0 < budget);
    r->ns = (t1 - t0) * 1e9 / r->calls;
    r->calls /= passes, r->sum /= passes;
    pcre2_match_data_free(md);
}

/* The executable regions of the process: one for each shared object
   loaded, since Fil-C maps nothing else executable. */
static int exec_regions(void)
{
    FILE *f = fopen("/proc/self/maps", "r");
    char line[4096], perms[8];
    int n = 0;
    while (f && fgets(line, sizeof line, f))
        n += sscanf(line, "%*s %7s", perms) == 1 && perms[2] == 'x';
    if (f)
        fclose(f);
    return n;
}

/* A program that compiles its patterns per request compiles the same
   pattern many times. Each copy of a pattern that main has compiled
   already is compiled here, given to pcre2_jit_compile, matched against
   the interpreter from the start of the subject and freed. It returns 1
   when a copy gets no function or answers otherwise, or when the
   compiles map anything executable, which they would if each loaded an
   object of its own. */
static int recompiled(const struct pat *pat, const char *subj, int times)
{
    int err, regions = exec_regions(), bad = 0;
    PCRE2_SIZE eo, len = strlen(subj);
    double ms = 0;
    pcre2_code *in = pcre2_compile((PCRE2_SPTR)pat->re, PCRE2_ZERO_TERMINATED, pat->opts, &err, &eo, NULL);
    pcre2_match_data *a = pcre2_match_data_create_from_pattern(in, NULL), *b = pcre2_match_data_create_from_pattern(in, NULL);
    PCRE2_SIZE *ova = pcre2_get_ovector_pointer(a), *ovb = pcre2_get_ovector_pointer(b);
    int rcb = pcre2_match(in, (PCRE2_SPTR)subj, len, 0, 0, b, NULL);
    for (int i = 0; i < times; i++) {
        pcre2_code *rx = pcre2_compile((PCRE2_SPTR)pat->re, PCRE2_ZERO_TERMINATED, pat->opts, &err, &eo, NULL);
        size_t size = 0;
        double t0 = now();
        int rc = pcre2_jit_compile(rx, PCRE2_JIT_COMPLETE);
        ms += (now() - t0) * 1e3;
        pcre2_pattern_info(rx, PCRE2_INFO_JITSIZE, &size);
        int rca = pcre2_match(rx, (PCRE2_SPTR)subj, len, 0, 0, a, NULL);
        bad += rc != 0 || size == 0 || rca != rcb || (rca > 0 && (ova[0] != ovb[0] || ova[1] != ovb[1]));
        pcre2_code_free(rx);
    }
    int more = exec_regions() - regions;
    printf("%s compiled again %d times in %.0f ms: %d differ, %d executable regions mapped\n", pat->name, times, ms,
           bad, more);
    pcre2_match_data_free(a);
    pcre2_match_data_free(b);
    pcre2_code_free(in);
    return bad || more;
}

int main(int argc, char **argv)
{
    double budget = argc > 1 ? atof(argv[1]) : 0.3, compile_ms = 0;
    size_t reps = 8, hl = sizeof(html) - 1, deep_len = 60000;
    char *big = malloc(hl * reps + 1), *abab = malloc(deep_len + 2);
    for (size_t i = 0; i < reps; i++)
        memcpy(big + i * hl, html, hl);
    big[hl * reps] = 0;
    for (size_t i = 0; i < deep_len; i++)
        abab[i] = "ab"[i & 1];
    strcpy(abab + deep_len, "!");

    uint32_t jit = 0;
    pcre2_config(PCRE2_CONFIG_JIT, &jit);
    if (!jit) {
        fprintf(stderr, "this libpcre2 reports no JIT: is PCRE2_RX_CACHE a directory only you can write?\n");
        return 2;
    }
    pcre2_match_context *tight = pcre2_match_context_create(NULL), *limited = pcre2_match_context_create(NULL);
    pcre2_set_heap_limit(tight, 1);
    pcre2_set_offset_limit(limited, 40);

    int status = 0, compiled = 0;
    size_t timed_pats = sizeof(pats) / sizeof(pats[0]), checked = timed_pats + sizeof(more) / sizeof(more[0]),
           all = checked + sizeof(hard) / sizeof(hard[0]);
    printf("%-10s %6s %6s %10s %10s %7s %10s\n", "pattern", "ms", "calls", "pcre2 ns", "hook ns", "speedup", "jit_match");
    for (size_t p = 0; p < all; p++) {
        const struct pat *pat = p < timed_pats ? &pats[p] : p < checked ? &more[p - timed_pats] : &hard[p - checked];
        int err;
        PCRE2_SIZE eo;
        if (argc > 2 && strcmp(argv[2], pat->name))
            continue;
        uint32_t opts = pat->opts | (p < checked ? 0 : PCRE2_USE_OFFSET_LIMIT);
        pcre2_code *rx = pcre2_compile((PCRE2_SPTR)pat->re, PCRE2_ZERO_TERMINATED, opts, &err, &eo, NULL);
        pcre2_code *in = pcre2_compile((PCRE2_SPTR)pat->re, PCRE2_ZERO_TERMINATED, opts, &err, &eo, NULL);
        /* Checked from every offset of one copy of the page, timed over
           all of them. */
        const char *subj = pat->subject ? pat->subject : p >= checked ? abab : html;
        const char *long_subj = pat->subject ? pat->subject : big;
        size_t len = strlen(subj), size = 0, step = len > 10000 ? 7919 : 1;
        uint32_t groups;
        double t0 = now();
        int rc = pcre2_jit_compile(rx, PCRE2_JIT_COMPLETE);
        double ms = (now() - t0) * 1e3;
        compile_ms += ms;
        pcre2_pattern_info(rx, PCRE2_INFO_JITSIZE, &size);
        pcre2_pattern_info(rx, PCRE2_INFO_CAPTURECOUNT, &groups);
        if (rc != 0 || size == 0) {
            printf("%-10s %6.1f interpreter (pcre2_jit_compile %d)\n", pat->name, ms, rc);
            continue;
        }
        compiled++;

        unsigned long n = 0, bad = 0;
        const uint32_t sizes[] = { groups + 1, 1, groups ? groups : 1, groups + 3 };
        for (size_t s = 0; s < sizeof sizes / sizeof sizes[0]; s++)
            bad += differences("pcre2_match", MATCH, rx, in, groups, sizes[s], 0, NULL, subj, len, step, &n);
        bad += differences("pcre2_jit_match", JIT_MATCH, rx, in, groups, groups + 1, 0, NULL, subj, len, step, &n);
        bad += differences("copied subject", MATCH, rx, in, groups, groups + 1, PCRE2_COPY_MATCHED_SUBJECT, NULL, subj,
                           len, step, &n);
        /* What the function does not handle goes to the interpreter. */
        const uint32_t options[] = { PCRE2_NOTEMPTY, PCRE2_NOTEMPTY_ATSTART, PCRE2_ANCHORED, PCRE2_NOTBOL, PCRE2_NOTEOL,
                                     PCRE2_PARTIAL_SOFT, PCRE2_NO_JIT };
        for (size_t o = 0; o < sizeof options / sizeof options[0]; o++)
            bad += differences("with an option", MATCH, rx, in, groups, groups + 1, options[o], NULL, subj, len, step, &n);
        bad += differences("heap limit", MATCH, rx, in, groups, groups + 1, 0, tight, subj, len, step, &n);
        if (p >= checked)
            bad += differences("offset limit", MATCH, rx, in, groups, groups + 1, 0, limited, subj, len, step, &n);
        bad += substitute_differs(rx, in, subj, len);
        if (bad) {
            printf("%-10s %lu of %lu checks differ\n", pat->name, bad, n);
            status = 1;
        } else if (p >= timed_pats) {
            printf("%-10s %6.1f agrees on %lu calls\n", pat->name, ms, n);
        } else {
            struct run a, b, c;
            timed(MATCH, in, long_subj, strlen(long_subj), budget, &a);
            timed(MATCH, rx, long_subj, strlen(long_subj), budget, &b);
            timed(JIT_MATCH, rx, long_subj, strlen(long_subj), budget, &c);
            if (a.calls != b.calls || a.sum != b.sum || a.calls != c.calls || a.sum != c.sum)
                status = 1;
            printf("%-10s %6.1f %6lu %10.1f %10.1f %6.1fx %10.1f\n", pat->name, ms, a.calls, a.ns, b.ns, a.ns / b.ns,
                   c.ns);
        }
        pcre2_code_free(rx);
        pcre2_code_free(in);
    }
    printf("%d patterns compiled, pcre2_jit_compile took %.0f ms in all\n", compiled, compile_ms);
    if (argc <= 2 && recompiled(&pats[0], html, 20))
        status = 1;
    return status;
}

/* The gate's driver for libnanofil (run.sh): many compiles in one
 * process, over the one arena the library keeps.
 *
 *   test_lib OUTDIR ROUNDS FILE...
 *
 * For each round, each FILE and each command (compile, compile-promoted,
 * compile-allocated), it calls nanofil_compile_ir on the file's text and
 * writes what `nanofil-backend COMMAND FILE` would print: the assembly to
 * OUTDIR/I.C.out, the reason with the command's prefix to OUTDIR/I.C.err,
 * and the status to OUTDIR/I.C.status, where I is the file's place in the
 * list and C the command's number. Round r takes the files in reverse
 * when r is odd, so a compile that depended on what the one before it left
 * in the arena would differ from round to round; every round overwrites
 * the same files, and each round's outputs are compared with the first's
 * (a difference is reported and makes the exit status 1).
 *
 *   test_lib --time N FILE COMMAND
 *
 * compiles FILE N times and prints the first call's time (which makes
 * the arena and runs the program's entry) and the best of the others. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "nanofil.h"

static char *slurp(const char *path, size_t *len)
{
    FILE *f = fopen(path, "rb");
    if (!f)
        return NULL;
    size_t cap = 1U << 16, n = 0;
    char *b = malloc(cap);
    for (size_t got; b && (got = fread(b + n, 1, cap - n, f)) > 0;) {
        n += got;
        if (n == cap)
            b = realloc(b, cap *= 2);
    }
    fclose(f);
    *len = n;
    return b;
}

static int spit(const char *path, const char *b, size_t n)
{
    FILE *f = fopen(path, "wb");
    if (!f)
        return -1;
    int ok = fwrite(b, 1, n, f) == n;
    return (fclose(f) == 0 && ok) ? 0 : -1;
}

static double now(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

static int timing(int n, const char *path, int cmd)
{
    size_t len;
    char *ir = slurp(path, &len);
    if (!ir) {
        perror(path);
        return 2;
    }
    double first = 0, best = 1e9;
    size_t out_len = 0;
    int status = 0;
    for (int i = 0; i < n; i++) {
        char *out;
        double t0 = now();
        status = nanofil_compile_ir(cmd, ir, len, &out, &out_len);
        double t = now() - t0;
        free(out);
        if (i == 0)
            first = t;
        else if (t < best)
            best = t;
    }
    printf("%s: status %d, %zu bytes; first %.1f ms, best of %d after it %.1f ms\n", path, status, out_len,
           first * 1e3, n - 1, n > 1 ? best * 1e3 : 0.0);
    free(ir);
    return 0;
}

int main(int argc, char **argv)
{
    if (argc == 5 && strcmp(argv[1], "--time") == 0)
        return timing(atoi(argv[2]), argv[3], atoi(argv[4]));
    if (argc < 4) {
        fprintf(stderr, "usage: test_lib OUTDIR ROUNDS FILE... | test_lib --time N FILE COMMAND\n");
        return 2;
    }
    const char *dir = argv[1];
    int rounds = atoi(argv[2]), nfiles = argc - 3, bad = 0;
    char path[4096];
    for (int r = 0; r < rounds; r++) {
        for (int k = 0; k < nfiles; k++) {
            int i = r % 2 ? nfiles - 1 - k : k;
            size_t len;
            char *ir = slurp(argv[3 + i], &len);
            if (!ir) {
                perror(argv[3 + i]);
                return 2;
            }
            for (int c = NANOFIL_COMPILE; c <= NANOFIL_COMPILE_ALLOCATED; c++) {
                char *out;
                size_t out_len;
                int status = nanofil_compile_ir(c, ir, len, &out, &out_len);
                if (status == NANOFIL_NOMEMORY) {
                    fprintf(stderr, "test_lib: %s: out of memory\n", argv[3 + i]);
                    return 2;
                }
                /* What nanofil-backend writes: the text on stdout, or the
                   reason on stderr after its prefix. */
                char err[8192] = "";
                if (status != NANOFIL_OK)
                    snprintf(err, sizeof err, "nanofil-backend: %s\n", out);
                const char *o = status == NANOFIL_OK ? out : "";
                size_t olen = status == NANOFIL_OK ? out_len : 0;
                char st[16];
                snprintf(st, sizeof st, "%d\n", status);
                if (r == 0) {
                    snprintf(path, sizeof path, "%s/%d.%d.out", dir, i, c);
                    spit(path, o, olen);
                    snprintf(path, sizeof path, "%s/%d.%d.err", dir, i, c);
                    spit(path, err, strlen(err));
                    snprintf(path, sizeof path, "%s/%d.%d.status", dir, i, c);
                    spit(path, st, strlen(st));
                } else {
                    size_t n0;
                    snprintf(path, sizeof path, "%s/%d.%d.out", dir, i, c);
                    char *prev = slurp(path, &n0);
                    if (!prev || n0 != olen || memcmp(prev, o, olen) != 0) {
                        fprintf(stderr, "test_lib: round %d: %s, command %d: not what round 0 gave\n", r,
                                argv[3 + i], c);
                        bad++;
                    }
                    free(prev);
                }
                free(out);
            }
            free(ir);
        }
    }
    return bad > 0;
}

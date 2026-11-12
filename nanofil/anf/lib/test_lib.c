/* The gate's driver for libnanofil (run.sh): many compiles in one
 * process, over the one arena the library keeps.
 *
 *   test_lib OUTDIR ROUNDS FILE...
 *
 * For each round, each FILE and each command (compile, compile-promoted,
 * compile-allocated, shared-allocated, object-allocated), it calls nanofil_compile_ir on the file's text and
 * writes what `nanofil-backend COMMAND FILE` would print: the assembly,
 * the shared object or the object's text to OUTDIR/I.C.out, the reason
 * with the command's prefix to OUTDIR/I.C.err, and the status to
 * OUTDIR/I.C.status, where I is the file's place in the
 * list and C the command's number. Round r takes the files in reverse
 * when r is odd, so a compile that depended on what the one before it left
 * in the arena would differ from round to round; every round overwrites
 * the same files, and each round's outputs are compared with the first's
 * (a difference is reported and makes the exit status 1).
 *
 *   test_lib --regex OUTDIR ROUNDS FILE.pl...
 *
 * does the same with the one command NANOFIL_REGEX on files of
 * pcre2_rx_terms.h's terms, and writes the reason to I.5.err as the
 * library gives it.
 *
 *   test_lib --time N FILE COMMAND
 *
 * compiles FILE N times and prints the first call's time (which makes
 * the arena and runs the program's entry) and the best of the others.
 *
 *   test_lib --load FILE...
 *
 * compiles each FILE with NANOFIL_SHARED_ALLOCATED, or NANOFIL_REGEX
 * when its name ends in .pl, loads the shared object with nanofil_load
 * and closes every other one with dlclose; then it loads every image
 * again. It exits 1 if an image is not loaded, if it is given the handle
 * of an image with other bytes, if an image with the bytes of an earlier
 * one or loaded again gets another handle, or if loading again maps
 * anything executable. */
#include <dlfcn.h>
#include <errno.h>
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

/* The executable mappings of the process: one for each shared object
   loaded, since Fil-C refuses PROT_EXEC to anything but the loader. */
static int exec_maps(void)
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

static int loading(int n, char **paths)
{
    int bad = 0;
    void **handles = calloc((size_t)n, sizeof *handles);
    char **images = calloc((size_t)n, sizeof *images);
    size_t *lens = calloc((size_t)n, sizeof *lens);
    for (int i = 0; i < n; i++) {
        size_t len;
        char *ir = slurp(paths[i], &len), *out;
        if (!ir || !handles || !images || !lens) {
            perror(paths[i]);
            return 2;
        }
        size_t k = strlen(paths[i]);
        int command = k > 3 && strcmp(paths[i] + k - 3, ".pl") == 0 ? NANOFIL_REGEX : NANOFIL_SHARED_ALLOCATED;
        int status = nanofil_compile_ir(command, ir, len, &out, &lens[i]);
        free(ir);
        if (status != NANOFIL_OK) {
            printf("not compiled %s: %s\n", paths[i], out ? out : "out of memory");
            free(out);
            bad++;
            continue;
        }
        void *h = nanofil_load(out, lens[i]);
        if (!h) {
            const char *why = dlerror();
            printf("NOT LOADED %s: %s\n", paths[i], why ? why : strerror(errno));
            free(out);
            bad++;
            continue;
        }
        images[i] = out;
        /* An object is shared by the images with its bytes and by no
           other. */
        for (int j = 0; j < i; j++) {
            int same = images[j] && lens[j] == lens[i] && memcmp(images[j], out, lens[i]) == 0;
            if (handles[j] == h && !same) {
                printf("SAME HANDLE %s as the different image of %s\n", paths[i], paths[j]);
                bad++;
            } else if (handles[j] != h && same) {
                printf("NOT REUSED %s: the image of %s has its bytes\n", paths[i], paths[j]);
                bad++;
            }
        }
        handles[i] = h;
        printf("loaded %s (%zu bytes)\n", paths[i], lens[i]);
        /* Every other object is closed at once, as a program frees a
           pattern, and the rest stay open, as it keeps one. */
        if (i % 2 && dlclose(h) != 0) {
            printf("NOT CLOSED %s: %s\n", paths[i], dlerror());
            bad++;
        }
    }
    /* Each image again, as a program compiles a pattern again: the
       handle it had, closed or not, and nothing new mapped. */
    int before = exec_maps(), again = 0;
    for (int i = 0; i < n; i++) {
        if (!images[i])
            continue;
        void *h = nanofil_load(images[i], lens[i]);
        size_t k = strlen(paths[i]);
        if (h != handles[i]) {
            printf("NOT REUSED %s: loaded again, it gave another handle\n", paths[i]);
            bad++;
        } else if (k > 3 && strcmp(paths[i] + k - 3, ".pl") == 0 && !dlsym(h, "rx_m")) {
            printf("NO rx_m in %s loaded again: %s\n", paths[i], dlerror());
            bad++;
        }
        again++;
        free(images[i]);
    }
    int after = exec_maps();
    if (after != before) {
        printf("NEW MAPPINGS: loading %d images again mapped %d more executable regions\n", again, after - before);
        bad++;
    }
    printf("loaded %d images again: their handles, %d executable regions before and after\n", again, before);
    free(handles);
    free(images);
    free(lens);
    return bad > 0;
}

int main(int argc, char **argv)
{
    if (argc >= 3 && strcmp(argv[1], "--load") == 0)
        return loading(argc - 2, argv + 2);
    if (argc == 5 && strcmp(argv[1], "--time") == 0)
        return timing(atoi(argv[2]), argv[3], atoi(argv[4]));
    int first = NANOFIL_COMPILE, last = NANOFIL_OBJECT_ALLOCATED;
    if (argc >= 2 && strcmp(argv[1], "--regex") == 0) {
        first = last = NANOFIL_REGEX;
        argc--;
        argv++;
    }
    if (argc < 4) {
        fprintf(stderr, "usage: test_lib [--regex] OUTDIR ROUNDS FILE... | test_lib --time N FILE COMMAND | "
                        "test_lib --load FILE...\n");
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
            for (int c = first; c <= last; c++) {
                char *out;
                size_t out_len;
                int status = nanofil_compile_ir(c, ir, len, &out, &out_len);
                if (status == NANOFIL_NOMEMORY) {
                    fprintf(stderr, "test_lib: %s: out of memory\n", argv[3 + i]);
                    return 2;
                }
                /* What nanofil-backend writes: the text on stdout, or the
                   reason on stderr after its prefix; for a regex, the
                   reason as it is. */
                char err[8192] = "";
                if (status != NANOFIL_OK)
                    snprintf(err, sizeof err, c == NANOFIL_REGEX ? "%s" : "nanofil-backend: %s\n", out);
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

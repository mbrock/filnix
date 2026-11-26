/* Arena driver for the Gallina C frontend lowered through λANF
 * (nanofil/anf/frontend/Drive.v -> AnfLower.v -> nanofil-backend).
 *
 *   anf-frontend [--c23] [--no-profile] [--clang PATH] [-I DIR] [-D SPEC]
 *                (lex | parse | count | pp | pp-parse) FILE
 *   anf-frontend [--c23] [--no-profile] [--clang PATH] [-I DIR] [-D SPEC]
 *                (bench | pp-only-bench | pp-bench) FILE...
 *
 * Mirrors nanofil/anf/backend/driver.c and nanofil/rocq/frontend/extraction/main.ml:
 * builds Drive.v's [mkargs cmd filename input extra] record in the 32-bit arena,
 * handles [Chunk] streaming and [NeedRead]/[NeedExists]/[NeedReal]/[NeedFeat]
 * I/O resumptions, and in preprocessor bench modes promotes the parsed [pp_env]
 * closure once into the major heap and rewinds the arena per file. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "../anf_arena.h"

uint32_t anf_main(uint32_t *arena, struct anf_state *st);
uint32_t anf_apply2(uint32_t *arena, struct anf_state *st, uint32_t fid, uint32_t a, uint32_t b);
const uint8_t *anf_str_bytes(const uint32_t *arena, uint32_t s, uint32_t *len);

static uint32_t env_words(const char *name, uint32_t dflt)
{
    const char *s = getenv(name);
    return s ? (uint32_t)strtoul(s, NULL, 0) : dflt;
}

static uint32_t apply(uint32_t *arena, struct anf_state *st, uint32_t clo, uint32_t arg)
{
    uint32_t idx = ANF_IDX(clo);
    return anf_apply2(arena, st, arena[idx + 1U], arena[idx + 2U], arg);
}

static uint32_t pair(uint32_t *arena, struct anf_state *st, uint32_t ord)
{
    uint32_t idx = anf_alloc_words(arena, st, 3U);
    uint32_t b = anf_root_pop(st), a = anf_root_pop(st);
    arena[idx] = ANF_HDR(2U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = a;
    arena[idx + 2U] = b;
    return ANF_BOX(idx);
}

static uint32_t quad(uint32_t *arena, struct anf_state *st, uint32_t ord)
{
    uint32_t idx = anf_alloc_words(arena, st, 5U);
    uint32_t d = anf_root_pop(st), c = anf_root_pop(st),
             b = anf_root_pop(st), a = anf_root_pop(st);
    arena[idx] = ANF_HDR(4U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = a;
    arena[idx + 2U] = b;
    arena[idx + 3U] = c;
    arena[idx + 4U] = d;
    return ANF_BOX(idx);
}

static uint8_t *read_all(const char *path, size_t *len_out)
{
    FILE *f = fopen(path, "rb");
    if (!f)
        return NULL;
    size_t cap = 1U << 16, n = 0;
    uint8_t *text = malloc(cap);
    for (size_t got; text && (got = fread(text + n, 1, cap - n, f)) > 0;) {
        n += got;
        if (n == cap)
            text = realloc(text, cap *= 2);
    }
    fclose(f);
    *len_out = n;
    return text;
}

static char *arena_str_dup(const uint32_t *arena, uint32_t s)
{
    uint32_t len = 0;
    const uint8_t *b = anf_str_bytes(arena, s, &len);
    char *out = malloc((size_t)len + 1U);
    if (!out)
        abort();
    if (len)
        memcpy(out, b, len);
    out[len] = '\0';
    return out;
}

static uint32_t build_pieces(uint32_t *arena, struct anf_state *st,
                             const uint8_t *text, size_t n, size_t piece)
{
    anf_root_push(st, ANF_IMM(0U));
    for (size_t end = n; end > 0;) {
        size_t start = (end - 1U) / piece * piece;
        uint32_t s = anf_bytes_from_buf(arena, st, text + start, (uint32_t)(end - start));
        uint32_t l = anf_root_pop(st);
        anf_root_push(st, s);
        anf_root_push(st, l);
        anf_root_push(st, pair(arena, st, 0U));
        end = start;
    }
    return anf_root_pop(st);
}

static uint32_t build_str_list(uint32_t *arena, struct anf_state *st,
                               char *const *items, int count)
{
    anf_root_push(st, ANF_IMM(0U));
    for (int i = count - 1; i >= 0; i--) {
        uint32_t s = anf_bytes_from_buf(arena, st, (const uint8_t *)items[i],
                                        (uint32_t)strlen(items[i]));
        uint32_t l = anf_root_pop(st);
        anf_root_push(st, s);
        anf_root_push(st, l);
        anf_root_push(st, pair(arena, st, 0U));
    }
    return anf_root_pop(st);
}

static uint32_t make_args(uint32_t *arena, struct anf_state *st, uint32_t cmd,
                          const char *fname_c, const uint8_t *text, size_t n,
                          size_t piece, char *const *extra_items, int extra_count)
{
    uint32_t extra = build_str_list(arena, st, extra_items, extra_count);
    anf_root_push(st, extra);
    uint32_t input = build_pieces(arena, st, text, n, piece);
    anf_root_push(st, input);
    uint32_t fname = anf_bytes_from_buf(arena, st, (const uint8_t *)fname_c,
                                        (uint32_t)strlen(fname_c));
    input = anf_root_pop(st);
    extra = anf_root_pop(st);
    anf_root_push(st, ANF_IMM(cmd));
    anf_root_push(st, fname);
    anf_root_push(st, input);
    anf_root_push(st, extra);
    return quad(arena, st, 0U);
}

static uint8_t *run_cmd_capture(const char *prog, char *const argv[],
                                const char *stdin_data, int capture_stderr,
                                size_t *len_out)
{
    int in_pipe[2] = {-1, -1};
    int out_pipe[2] = {-1, -1};
    if (stdin_data && pipe(in_pipe) != 0)
        return NULL;
    if (pipe(out_pipe) != 0) {
        if (in_pipe[0] >= 0) {
            close(in_pipe[0]);
            close(in_pipe[1]);
        }
        return NULL;
    }
    pid_t pid = fork();
    if (pid < 0)
        return NULL;
    if (pid == 0) {
        int devnull = open("/dev/null", O_RDWR);
        if (stdin_data) {
            dup2(in_pipe[0], STDIN_FILENO);
            close(in_pipe[0]);
            close(in_pipe[1]);
        } else if (devnull >= 0) {
            dup2(devnull, STDIN_FILENO);
        }
        if (capture_stderr) {
            if (devnull >= 0)
                dup2(devnull, STDOUT_FILENO);
            dup2(out_pipe[1], STDERR_FILENO);
        } else {
            dup2(out_pipe[1], STDOUT_FILENO);
            if (devnull >= 0)
                dup2(devnull, STDERR_FILENO);
        }
        close(out_pipe[0]);
        close(out_pipe[1]);
        if (devnull >= 0)
            close(devnull);
        execvp(prog, argv);
        _exit(127);
    }
    close(out_pipe[1]);
    if (stdin_data) {
        close(in_pipe[0]);
        size_t slen = strlen(stdin_data), off = 0;
        while (off < slen) {
            ssize_t w = write(in_pipe[1], stdin_data + off, slen - off);
            if (w <= 0)
                break;
            off += (size_t)w;
        }
        close(in_pipe[1]);
    }
    size_t cap = 4096, n = 0;
    uint8_t *buf = malloc(cap);
    for (;;) {
        if (n + 4096 >= cap) {
            cap *= 2;
            buf = realloc(buf, cap);
        }
        ssize_t r = read(out_pipe[0], buf + n, cap - n - 1);
        if (r <= 0)
            break;
        n += (size_t)r;
    }
    close(out_pipe[0]);
    buf[n] = '\0';
    int status = 0;
    waitpid(pid, &status, 0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        free(buf);
        return NULL;
    }
    *len_out = n;
    return buf;
}

static const char *const default_feats[][2] = {
    {"__has_attribute", "__nothrow__"},
    {"__has_attribute", "__cold__"},
    {"__has_attribute", "__malloc__"},
    {"__has_attribute", "__alloc_align__"},
    {"__has_attribute", "__pure__"},
    {"__has_attribute", "__const__"},
    {"__has_attribute", "__unused__"},
    {"__has_attribute", "__used__"},
    {"__has_attribute", "__deprecated__"},
    {"__has_attribute", "__format_arg__"},
    {"__has_attribute", "__format__"},
    {"__has_attribute", "__nonnull__"},
    {"__has_attribute", "__returns_nonnull__"},
    {"__has_attribute", "__warn_unused_result__"},
    {"__has_attribute", "__always_inline__"},
    {"__has_attribute", "__artificial__"},
    {"__has_attribute", "__indirect_return__"},
    {"__has_builtin", "__builtin_expect"},
    {"__has_builtin", "__builtin_FILE"},
    {"__has_builtin", "__builtin_fclose"},
    {"__has_extension", "__attribute_deprecated_with_message__"},
    {"__has_extension", "c_generic_selections"},
    {"__has_feature", "modules"},
    {"__building_module", "_Builtin_stddef"},
};

static char *query_single_feature(const char *clang, const char *op, const char *name)
{
    if (!clang)
        return strdup("0");
    size_t qlen = strlen(op) + strlen(name) + 4;
    char *q = malloc(qlen);
    snprintf(q, qlen, "%s(%s)\n", op, name);
    char *argv[] = {(char *)clang, "-E", "-P", "-x", "c", "-", NULL};
    size_t out_len = 0;
    uint8_t *out = run_cmd_capture(clang, argv, q, 0, &out_len);
    free(q);
    if (!out)
        return strdup("0");
    char *p = (char *)out;
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')
        p++;
    char *e = p;
    while (*e && *e != ' ' && *e != '\t' && *e != '\r' && *e != '\n')
        e++;
    *e = '\0';
    char *res = (*p) ? strdup(p) : strdup("0");
    free(out);
    return res;
}

static uint32_t drive_out(uint32_t *arena, struct anf_state *st, uint32_t out,
                          size_t piece, const char *clang,
                          FILE *out_stream, char *capture_buf, size_t capture_cap)
{
    size_t cap_pos = 0;
    for (;;) {
        uint32_t ord = ANF_HDR_ORD(arena[ANF_IDX(out)]);
        if (ord == 0U || ord == 6U) {
            if (capture_buf && capture_cap > 0)
                capture_buf[cap_pos] = '\0';
            return out;
        }
        if (ord == 1U) {
            /* Chunk (ps, next) */
            for (uint32_t ps = arena[ANF_IDX(out) + 1U]; !ANF_IS_IMM(ps);
                 ps = arena[ANF_IDX(ps) + 2U]) {
                uint32_t len;
                const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(ps) + 1U], &len);
                if (len) {
                    if (out_stream)
                        fwrite(b, 1, len, out_stream);
                    if (capture_buf && cap_pos + len < capture_cap - 1U) {
                        memcpy(capture_buf + cap_pos, b, len);
                        cap_pos += len;
                    }
                }
            }
            out = apply(arena, st, arena[ANF_IDX(out) + 2U], ANF_IMM(0U));
        } else if (ord == 2U) {
            /* NeedRead (path, next) */
            char *path = arena_str_dup(arena, arena[ANF_IDX(out) + 1U]);
            anf_root_push(st, arena[ANF_IDX(out) + 2U]);
            size_t flen = 0;
            uint8_t *buf = read_all(path, &flen);
            free(path);
            uint32_t arg;
            if (!buf) {
                anf_root_push(st, ANF_IMM(0U));
                anf_root_push(st, ANF_IMM(0U));
                arg = pair(arena, st, 0U);
            } else {
                uint32_t pieces = build_pieces(arena, st, buf, flen, piece);
                free(buf);
                anf_root_push(st, ANF_IMM(1U));
                anf_root_push(st, pieces);
                arg = pair(arena, st, 0U);
            }
            uint32_t next = anf_root_pop(st);
            out = apply(arena, st, next, arg);
        } else if (ord == 3U) {
            /* NeedExists (path, next) */
            char *path = arena_str_dup(arena, arena[ANF_IDX(out) + 1U]);
            struct stat sb;
            uint32_t exists = (stat(path, &sb) == 0 && S_ISREG(sb.st_mode)) ? 1U : 0U;
            free(path);
            out = apply(arena, st, arena[ANF_IDX(out) + 2U], ANF_IMM(exists));
        } else if (ord == 4U) {
            /* NeedReal (path, next) */
            char *path = arena_str_dup(arena, arena[ANF_IDX(out) + 1U]);
            anf_root_push(st, arena[ANF_IDX(out) + 2U]);
            char rp_buf[PATH_MAX];
            const char *res = realpath(path, rp_buf);
            if (!res)
                res = path;
            uint32_t s = anf_bytes_from_buf(arena, st, (const uint8_t *)res,
                                            (uint32_t)strlen(res));
            free(path);
            uint32_t next = anf_root_pop(st);
            out = apply(arena, st, next, s);
        } else if (ord == 5U) {
            /* NeedFeat (op, name, next) */
            char *op = arena_str_dup(arena, arena[ANF_IDX(out) + 1U]);
            char *name = arena_str_dup(arena, arena[ANF_IDX(out) + 2U]);
            anf_root_push(st, arena[ANF_IDX(out) + 3U]);
            char *ans = query_single_feature(clang, op, name);
            free(op);
            free(name);
            uint32_t s = anf_bytes_from_buf(arena, st, (const uint8_t *)ans,
                                            (uint32_t)strlen(ans));
            free(ans);
            uint32_t next = anf_root_pop(st);
            out = apply(arena, st, next, s);
        } else {
            fprintf(stderr, "anf-frontend: unexpected out constructor %u\n", ord);
            abort();
        }
    }
}

static uint32_t build_env_closure(uint32_t *arena, struct anf_state *st,
                                  uint32_t run_clo, size_t piece,
                                  int no_profile, const char *clang,
                                  char *const *inc_dirs, int n_incs,
                                  char *const *defines, int n_defs)
{
    uint8_t *defs_buf = NULL;
    size_t defs_len = 0;
    uint8_t *verbose_buf = NULL;
    size_t verbose_len = 0;

    int n_default = (int)(sizeof(default_feats) / sizeof(default_feats[0]));
    int extra_cap = n_incs + n_defs + n_default + 4;
    char **extra = calloc((size_t)extra_cap, sizeof(char *));
    int n_extra = 0;

    for (int i = 0; i < n_incs; i++) {
        size_t l = strlen(inc_dirs[i]) + 2;
        extra[n_extra] = malloc(l);
        snprintf(extra[n_extra], l, "I%s", inc_dirs[i]);
        n_extra++;
    }
    for (int i = 0; i < n_defs; i++) {
        size_t l = strlen(defines[i]) + 2;
        extra[n_extra] = malloc(l);
        snprintf(extra[n_extra], l, "D%s", defines[i]);
        n_extra++;
    }

    if (!no_profile) {
        char *dm_argv[] = {(char *)clang, "-dM", "-E", "-x", "c", "/dev/null", NULL};
        defs_buf = run_cmd_capture(clang, dm_argv, NULL, 0, &defs_len);
        if (!defs_buf) {
            fprintf(stderr, "anf-frontend: failed running %s -dM\n", clang);
            exit(2);
        }
        char *v_argv[] = {(char *)clang, "-E", "-v", "-x", "c", "/dev/null", NULL};
        verbose_buf = run_cmd_capture(clang, v_argv, NULL, 1, &verbose_len);
        if (!verbose_buf) {
            fprintf(stderr, "anf-frontend: failed running %s -E -v\n", clang);
            exit(2);
        }
        size_t qcap = 2048;
        char *qbuf = malloc(qcap);
        size_t qpos = 0;
        for (int i = 0; i < n_default; i++) {
            qpos += (size_t)snprintf(qbuf + qpos, qcap - qpos, "%s(%s)\n",
                                     default_feats[i][0], default_feats[i][1]);
        }
        char *f_argv[] = {(char *)clang, "-E", "-P", "-x", "c", "-", NULL};
        size_t fout_len = 0;
        uint8_t *fout = run_cmd_capture(clang, f_argv, qbuf, 0, &fout_len);
        free(qbuf);
        if (fout) {
            char *p = (char *)fout;
            for (int i = 0; i < n_default; i++) {
                while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')
                    p++;
                if (!*p)
                    break;
                char *e = p;
                while (*e && *e != ' ' && *e != '\t' && *e != '\r' && *e != '\n')
                    e++;
                char saved = *e;
                *e = '\0';
                size_t fl = strlen(default_feats[i][0]) + strlen(default_feats[i][1]) + strlen(p) + 4;
                extra[n_extra] = malloc(fl);
                snprintf(extra[n_extra], fl, "F%s %s %s",
                         default_feats[i][0], default_feats[i][1], p);
                n_extra++;
                *e = saved;
                p = e;
            }
            free(fout);
        }
    }

    uint32_t a = make_args(arena, st, 5U, verbose_buf ? (const char *)verbose_buf : "",
                           defs_buf, defs_len, piece, extra, n_extra);
    free(defs_buf);
    free(verbose_buf);
    for (int i = 0; i < n_extra; i++)
        free(extra[i]);
    free(extra);

    uint32_t out = apply(arena, st, run_clo, a);
    if (ANF_HDR_ORD(arena[ANF_IDX(out)]) != 6U) {
        fprintf(stderr, "anf-frontend: build_env did not return Ready\n");
        exit(2);
    }
    return arena[ANF_IDX(out) + 1U];
}

static int collect_lower_opts(char *out[4])
{
    int n = 0;
    const char *v = getenv("NANOFIL_VECTORS");
    if (v && strcmp(v, "0") == 0)
        out[n++] = "V0";
    const char *std = getenv("NANOFIL_STD");
    if (std && strcmp(std, "gnu89") == 0)
        out[n++] = "G1";
    const char *comm = getenv("NANOFIL_COMMON");
    if (comm && strcmp(comm, "1") == 0)
        out[n++] = "C1";
    const char *merr = getenv("NANOFIL_MATH_ERRNO");
    if (merr && strcmp(merr, "0") == 0)
        out[n++] = "M0";
    return n;
}

static double now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1e6;
}

int main(int argc, char **argv)
{
    int c23 = 0, no_profile = 0;
    const char *clang_opt = NULL;
    char **inc_dirs = calloc((size_t)argc + 1, sizeof(char *));
    char **defines = calloc((size_t)argc + 1, sizeof(char *));
    char **pos = calloc((size_t)argc + 1, sizeof(char *));
    int n_incs = 0, n_defs = 0, n_pos = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--c23") == 0) {
            c23 = 1;
        } else if (strcmp(argv[i], "--no-profile") == 0) {
            no_profile = 1;
        } else if (strcmp(argv[i], "--clang") == 0 && i + 1 < argc) {
            clang_opt = argv[++i];
        } else if (strcmp(argv[i], "-I") == 0 && i + 1 < argc) {
            inc_dirs[n_incs++] = argv[++i];
        } else if (strncmp(argv[i], "-I", 2) == 0 && argv[i][2] != '\0') {
            inc_dirs[n_incs++] = argv[i] + 2;
        } else if (strcmp(argv[i], "-D") == 0 && i + 1 < argc) {
            defines[n_defs++] = argv[++i];
        } else if (strncmp(argv[i], "-D", 2) == 0 && argv[i][2] != '\0') {
            defines[n_defs++] = argv[i] + 2;
        } else {
            pos[n_pos++] = argv[i];
        }
    }

    if (n_pos < 2) {
        fprintf(stderr,
                "usage: anf-frontend [--c23] [--no-profile] [--clang PATH] [-I DIR] [-D SPEC]\n"
                "                    (lex|lex-c23|parse|parse-c23|count|cc-ir|cc-layouts|\n"
                "                     pp|pp-parse|pp-cc-ir|pp-cc-layouts FILE |\n"
                "                     bench|cc-ir-bench|pp-only-bench|pp-bench|pp-cc-ir-bench FILE...)\n");
        return 2;
    }

    const char *clang = NULL;
    if (!no_profile) {
        if (clang_opt)
            clang = clang_opt;
        else {
            const char *e = getenv("FILCC");
            clang = (e && *e) ? e : "clang";
        }
    }

    uint32_t *arena;
    struct anf_state *st;
    if (anf_arena_init(&arena, &st, env_words("ANF_SLAB", 1U << 28),
                       env_words("ANF_NURSERY", ANF_DEFAULT_NURSERY),
                       env_words("ANF_ROOTS", 1U << 24))) {
        fprintf(stderr, "anf-frontend: the arena was not made\n");
        return 2;
    }
    size_t piece = env_words("ANF_PIECE", 1U << 20);
    uint32_t release_words = env_words("ANF_RELEASE", 1U << 22);

    anf_root_push(st, anf_main(arena, st));
    anf_minor_gc(arena, anf_roots(st), st);
    uint32_t run_clo = anf_root_pop(st);
    uint32_t mark = st->major_idx;

    const char *cmd_str = pos[0];

    char *lower_opts[4];
    int n_lower_opts = collect_lower_opts(lower_opts);

    if (strcmp(cmd_str, "bench") == 0 || strcmp(cmd_str, "cc-ir-bench") == 0) {
        int is_ir = (strcmp(cmd_str, "cc-ir-bench") == 0);
        uint32_t subcmd = is_ir ? 10U : 4U;
        int nfiles = n_pos - 1;
        int ok = 0, err = 0;
        long long total_toks = 0, total_items = 0;
        double t0 = now_ms();
        for (int i = 0; i < nfiles; i++) {
            size_t flen = 0;
            uint8_t *buf = read_all(pos[1 + i], &flen);
            if (!buf) {
                perror(pos[1 + i]);
                return 2;
            }
            anf_arena_rewind(arena, st, mark, release_words);
            uint32_t a = make_args(arena, st, subcmd, pos[1 + i], buf, flen, piece,
                                   is_ir ? lower_opts : NULL, is_ir ? n_lower_opts : 0);
            free(buf);
            char line[128];
            uint32_t out = drive_out(arena, st, apply(arena, st, run_clo, a),
                                     piece, NULL, NULL, line, sizeof(line));
            uint32_t code = ANF_IMM_U31(arena[ANF_IDX(out) + 1U]);
            if (code == 0U) {
                long long nt = 0, ni = 0;
                if (is_ir) {
                    if (sscanf(line, "ok %lld", &ni) == 1)
                        total_items += ni;
                } else {
                    if (sscanf(line, "ok %lld %lld", &nt, &ni) == 2) {
                        total_toks += nt;
                        total_items += ni;
                    }
                }
                ok++;
            } else {
                err++;
            }
        }
        double dt = now_ms() - t0;
        if (is_ir) {
            printf("Gallina-λANF-FilC cc-ir: %d ok, %d err | %lld ir-items | %.1f ms (gc=%llu, major_hwm=%u words)\n",
                   ok, err, total_items, dt,
                   (unsigned long long)st->gc_count, st->major_hwm);
        } else {
            printf("Gallina-λANF-FilC frontend: %d ok, %d err | %lld ok-tokens, %lld items | %.1f ms (gc=%llu, major_hwm=%u words)\n",
                   ok, err, total_toks, total_items, dt,
                   (unsigned long long)st->gc_count, st->major_hwm);
        }
        return 0;
    }

    if (strcmp(cmd_str, "pp-bench") == 0 || strcmp(cmd_str, "pp-only-bench") == 0
        || strcmp(cmd_str, "pp-cc-ir-bench") == 0) {
        int is_ir = (strcmp(cmd_str, "pp-cc-ir-bench") == 0);
        int parse_too = (strcmp(cmd_str, "pp-bench") == 0);
        uint32_t subcmd = is_ir ? 10U : (parse_too ? 4U : 5U);
        double tp0 = now_ms();
        uint32_t env_clo = build_env_closure(arena, st, run_clo, piece,
                                             no_profile, clang,
                                             inc_dirs, n_incs, defines, n_defs);
        anf_root_push(st, env_clo);
        anf_minor_gc(arena, anf_roots(st), st);
        env_clo = anf_root_pop(st);
        uint32_t env_mark = st->major_idx;
        double t0 = now_ms();

        int nfiles = n_pos - 1;
        int ok = 0, err = 0;
        long long total_toks = 0, total_items = 0;
        for (int i = 0; i < nfiles; i++) {
            anf_arena_rewind(arena, st, env_mark, release_words);
            uint32_t a = make_args(arena, st, subcmd, pos[1 + i], NULL, 0, piece,
                                   is_ir ? lower_opts : NULL, is_ir ? n_lower_opts : 0);
            char line[128];
            uint32_t out = drive_out(arena, st, apply(arena, st, env_clo, a),
                                     piece, clang, NULL, line, sizeof(line));
            uint32_t code = ANF_IMM_U31(arena[ANF_IDX(out) + 1U]);
            if (code == 0U) {
                long long nt = 0, ni = 0;
                if (is_ir) {
                    if (sscanf(line, "ok %lld", &ni) == 1)
                        total_items += ni;
                } else if (sscanf(line, "ok %lld %lld", &nt, &ni) == 2) {
                    total_toks += nt;
                    total_items += ni;
                }
                ok++;
            } else {
                err++;
            }
        }
        double dt = now_ms() - t0;
        double dprof = t0 - tp0;
        if (is_ir) {
            printf("Gallina-λANF-FilC pp-cc-ir: %d ok, %d err | %lld ir-items | %.1f ms (profile %.1f ms, gc=%llu, major_hwm=%u words)\n",
                   ok, err, total_items, dt, dprof,
                   (unsigned long long)st->gc_count, st->major_hwm);
        } else {
            printf("Gallina-λANF-FilC %s: %d ok, %d err | %lld tokens, %lld items | %.1f ms (profile %.1f ms, gc=%llu, major_hwm=%u words)\n",
                   parse_too ? "pp+parse" : "pp-only",
                   ok, err, total_toks, total_items, dt, dprof,
                   (unsigned long long)st->gc_count, st->major_hwm);
        }
        return 0;
    }

    if (n_pos == 2 && (strcmp(cmd_str, "pp") == 0 || strcmp(cmd_str, "pp-parse") == 0
                       || strcmp(cmd_str, "pp-cc-ir") == 0 || strcmp(cmd_str, "pp-cc-layouts") == 0)) {
        uint32_t subcmd;
        if (strcmp(cmd_str, "pp") == 0)
            subcmd = c23 ? 1U : 0U;
        else if (strcmp(cmd_str, "pp-parse") == 0)
            subcmd = c23 ? 3U : 2U;
        else if (strcmp(cmd_str, "pp-cc-ir") == 0)
            subcmd = c23 ? 7U : 6U;
        else
            subcmd = c23 ? 9U : 8U;
        uint32_t env_clo = build_env_closure(arena, st, run_clo, piece,
                                             no_profile, clang,
                                             inc_dirs, n_incs, defines, n_defs);
        anf_root_push(st, env_clo);
        uint32_t a = make_args(arena, st, subcmd, pos[1], NULL, 0, piece,
                               lower_opts, n_lower_opts);
        env_clo = anf_root_pop(st);
        uint32_t out = drive_out(arena, st, apply(arena, st, env_clo, a),
                                 piece, clang, stdout, NULL, 0);
        fflush(stdout);
        uint32_t code = ANF_IMM_U31(arena[ANF_IDX(out) + 1U]);
        if (code != 0U) {
            uint32_t len;
            const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(out) + 2U], &len);
            if (len)
                fwrite(b, 1, len, stderr);
            fputc('\n', stderr);
        }
        return (int)code;
    }

    uint32_t cmd = 5U;
    if (n_pos == 2) {
        if (strcmp(cmd_str, "lex") == 0) cmd = c23 ? 1U : 0U;
        else if (strcmp(cmd_str, "lex-c23") == 0) cmd = 1U;
        else if (strcmp(cmd_str, "parse") == 0) cmd = c23 ? 3U : 2U;
        else if (strcmp(cmd_str, "parse-c23") == 0) cmd = 3U;
        else if (strcmp(cmd_str, "count") == 0) cmd = 4U;
        else if (strcmp(cmd_str, "cc-ir") == 0) cmd = c23 ? 7U : 6U;
        else if (strcmp(cmd_str, "cc-layouts") == 0) cmd = c23 ? 9U : 8U;
    }
    if (cmd == 5U) {
        fprintf(stderr, "usage: anf-frontend (lex|parse|count|cc-ir|cc-layouts|pp|pp-parse|pp-cc-ir|pp-cc-layouts FILE | bench|cc-ir-bench|pp-only-bench|pp-bench|pp-cc-ir-bench FILE...)\n");
        return 2;
    }
    size_t n = 0;
    uint8_t *text = read_all(pos[1], &n);
    if (!text) {
        perror(pos[1]);
        return 2;
    }
    uint32_t a = make_args(arena, st, cmd, pos[1], text, n, piece,
                           lower_opts, n_lower_opts);
    free(text);
    uint32_t out = drive_out(arena, st, apply(arena, st, run_clo, a),
                             piece, NULL, stdout, NULL, 0);
    fflush(stdout);
    uint32_t code = ANF_IMM_U31(arena[ANF_IDX(out) + 1U]);
    if (code != 0U) {
        uint32_t len;
        const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(out) + 2U], &len);
        if (len)
            fwrite(b, 1, len, stderr);
        fputc('\n', stderr);
    }
    if (getenv("ANF_STATS"))
        fprintf(stderr, "anf: %llu minor collections, %llu words promoted, major heap %u words\n",
                (unsigned long long)st->gc_count, (unsigned long long)st->promoted_words, st->major_hwm);
    return (int)code;
}

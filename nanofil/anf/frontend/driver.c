/* Arena driver for the Gallina C frontend lowered through λANF
 * (nanofil/rocq/frontend/anf/Drive.v -> AnfLower.v -> nanofil-backend).
 *
 *   anf-frontend lex|lex-c23|parse|parse-c23|count FILE.c
 *   anf-frontend bench FILE.c...
 *
 * Mirrors nanofil/anf/backend/driver.c and nanofil/anf/lib/libnanofil.c:
 * builds Drive.v's [mkargs cmd filename input] record in the 32-bit arena,
 * applies [run], and writes each streamed Chunk's string parts to stdout.
 * In `bench` mode, promotes [run] once and rewinds the arena per file. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
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

static uint32_t triple(uint32_t *arena, struct anf_state *st, uint32_t ord)
{
    uint32_t idx = anf_alloc_words(arena, st, 4U);
    uint32_t c = anf_root_pop(st), b = anf_root_pop(st), a = anf_root_pop(st);
    arena[idx] = ANF_HDR(3U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = a;
    arena[idx + 2U] = b;
    arena[idx + 3U] = c;
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

static uint32_t run_one(uint32_t *arena, struct anf_state *st, uint32_t run_clo,
                        uint32_t cmd, const char *path, const uint8_t *text, size_t n,
                        size_t piece)
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
    uint32_t fname = anf_bytes_from_buf(arena, st, (const uint8_t *)path, (uint32_t)strlen(path));
    uint32_t input = anf_root_pop(st);
    anf_root_push(st, ANF_IMM(cmd));
    anf_root_push(st, fname);
    anf_root_push(st, input);
    uint32_t args = triple(arena, st, 0U);
    return apply(arena, st, run_clo, args);
}

static double now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1e6;
}

int main(int argc, char **argv)
{
    if (argc < 3) {
        fprintf(stderr, "usage: anf-frontend (lex|lex-c23|parse|parse-c23|count FILE | bench FILE...)\n");
        return 2;
    }
    uint32_t *arena;
    struct anf_state *st;
    if (anf_arena_init(&arena, &st, env_words("ANF_SLAB", 1U << 28),
                       env_words("ANF_NURSERY", ANF_DEFAULT_NURSERY), env_words("ANF_ROOTS", 1U << 24))) {
        fprintf(stderr, "anf-frontend: the arena was not made\n");
        return 2;
    }
    size_t piece = env_words("ANF_PIECE", 1U << 20);
    uint32_t release_words = env_words("ANF_RELEASE", 1U << 22);

    anf_root_push(st, anf_main(arena, st));
    anf_minor_gc(arena, anf_roots(st), st);
    uint32_t run_clo = anf_root_pop(st);
    uint32_t mark = st->major_idx;

    if (strcmp(argv[1], "bench") == 0) {
        int nfiles = argc - 2;
        int ok = 0, err = 0;
        long long total_toks = 0, total_items = 0;
        double t0 = now_ms();
        for (int i = 0; i < nfiles; i++) {
            size_t flen = 0;
            uint8_t *buf = read_all(argv[2 + i], &flen);
            if (!buf) {
                perror(argv[2 + i]);
                return 2;
            }
            anf_arena_rewind(arena, st, mark, release_words);
            uint32_t out = run_one(arena, st, run_clo, 4U, argv[2 + i], buf, flen, piece);
            free(buf);
            char line[128];
            size_t pos = 0;
            while (ANF_HDR_ORD(arena[ANF_IDX(out)]) == 1U) {
                for (uint32_t ps = arena[ANF_IDX(out) + 1U]; !ANF_IS_IMM(ps); ps = arena[ANF_IDX(ps) + 2U]) {
                    uint32_t len;
                    const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(ps) + 1U], &len);
                    if (pos + len < sizeof(line) - 1U) {
                        memcpy(line + pos, b, len);
                        pos += len;
                    }
                }
                out = apply(arena, st, arena[ANF_IDX(out) + 2U], ANF_IMM(0U));
            }
            line[pos] = '\0';
            uint32_t code = ANF_IMM_U31(arena[ANF_IDX(out) + 1U]);
            if (code == 0U) {
                long long nt = 0, ni = 0;
                if (sscanf(line, "ok %lld %lld", &nt, &ni) == 2) {
                    total_toks += nt;
                    total_items += ni;
                }
                ok++;
            } else {
                err++;
            }
        }
        double dt = now_ms() - t0;
        printf("Gallina-λANF-FilC frontend: %d ok, %d err | %lld ok-tokens, %lld items | %.1f ms (gc=%llu, major_hwm=%u words)\n",
               ok, err, total_toks, total_items, dt,
               (unsigned long long)st->gc_count, st->major_hwm);
        return 0;
    }

    static const char *const cmds[] = {"lex", "lex-c23", "parse", "parse-c23", "count"};
    uint32_t cmd = 5U;
    for (uint32_t i = 0U; argc == 3 && i < 5U; i++)
        if (strcmp(argv[1], cmds[i]) == 0)
            cmd = i;
    if (cmd == 5U) {
        fprintf(stderr, "usage: anf-frontend (lex|lex-c23|parse|parse-c23|count FILE | bench FILE...)\n");
        return 2;
    }
    size_t n = 0;
    uint8_t *text = read_all(argv[2], &n);
    if (!text) {
        perror(argv[2]);
        return 2;
    }
    uint32_t out = run_one(arena, st, run_clo, cmd, argv[2], text, n, piece);
    free(text);

    while (ANF_HDR_ORD(arena[ANF_IDX(out)]) == 1U) {
        for (uint32_t ps = arena[ANF_IDX(out) + 1U]; !ANF_IS_IMM(ps); ps = arena[ANF_IDX(ps) + 2U]) {
            uint32_t len;
            const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(ps) + 1U], &len);
            if (len)
                fwrite(b, 1, len, stdout);
        }
        out = apply(arena, st, arena[ANF_IDX(out) + 2U], ANF_IMM(0U));
    }
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

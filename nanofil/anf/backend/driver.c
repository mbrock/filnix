/* The Gallina backend (rocq/backend) lowered through λANF
 * (nanofil/docs/lambda-anf.md, M3): what `nanofil-backend compile`,
 * `compile-promoted` and `compile-allocated FILE.ir` do, with Drive.v's
 * [run], lowered by anf/lower/AnfLower.v, doing all of it but reading
 * the file and writing the bytes.
 *
 *   anf-backend compile|compile-promoted|compile-allocated FILE.ir
 *
 * The program's value is the closure of [run]. This reads the file in
 * pieces of 1 MB (ANF_PIECE bytes), as main.ml does, makes [run]'s
 * argument (the command's number and the list of pieces, each a string)
 * and applies [run] to it, then walks the stream it gives: each Chunk's
 * parts go to stdout before its next is applied to tt; Done ends the run
 * with its status and, when that is not 0, its reason on stderr, as
 * main.ml ends it.
 *
 * A closure is a block of its code's fid and its environment, which
 * CertiRocq passes as the first argument; anf_apply2 is the dispatcher of
 * functions of two arguments. The arena is sized as in anf/lower/driver.c
 * (ANF_NURSERY, ANF_SLAB, ANF_ROOTS), and ANF_STATS=1 reports its
 * collections on stderr. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
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

/* A block of two scanned fields, the ordinal ord, from the values on top
 * of the shadow roots (a under b), which it pops. */
static uint32_t pair(uint32_t *arena, struct anf_state *st, uint32_t ord)
{
    uint32_t idx = anf_alloc_words(arena, st, 3U);
    uint32_t b = anf_root_pop(st), a = anf_root_pop(st);
    arena[idx] = ANF_HDR(2U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = a;
    arena[idx + 2U] = b;
    return ANF_BOX(idx);
}

int main(int argc, char **argv)
{
    static const char *const cmds[] = {"compile", "compile-promoted", "compile-allocated"};
    uint32_t cmd = 3U;
    for (uint32_t i = 0U; argc == 3 && i < 3U; i++)
        if (strcmp(argv[1], cmds[i]) == 0)
            cmd = i;
    if (cmd == 3U) {
        fprintf(stderr, "usage: anf-backend compile|compile-promoted|compile-allocated FILE.ir\n");
        return 2;
    }
    FILE *f = fopen(argv[2], "rb");
    if (!f) {
        perror(argv[2]);
        return 2;
    }
    size_t cap = 1U << 20, n = 0;
    uint8_t *text = malloc(cap);
    for (size_t got; text && (got = fread(text + n, 1, cap - n, f)) > 0;) {
        n += got;
        if (n == cap)
            text = realloc(text, cap *= 2);
    }
    fclose(f);
    if (!text) {
        fprintf(stderr, "anf-backend: out of memory\n");
        return 2;
    }

    uint32_t *arena;
    struct anf_state *st;
    if (anf_arena_init(&arena, &st, env_words("ANF_SLAB", 1U << 28),
                       env_words("ANF_NURSERY", ANF_DEFAULT_NURSERY), env_words("ANF_ROOTS", 1U << 24))) {
        fprintf(stderr, "anf-backend: the arena was not made\n");
        return 2;
    }
    /* First, on the fresh arena: it copies the constants' pool to the
     * bottom of the major heap. */
    anf_root_push(st, anf_main(arena, st));

    /* The pieces, last first, consed onto nil. */
    size_t piece = env_words("ANF_PIECE", 1U << 20);
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
    free(text);
    uint32_t input = anf_root_pop(st);
    anf_root_push(st, ANF_IMM(cmd));
    anf_root_push(st, input);
    uint32_t args = pair(arena, st, 0U);
    uint32_t out = apply(arena, st, anf_root_pop(st), args);

    /* Done (ordinal 0) or Chunk (ordinal 1). */
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
        fputs("nanofil-backend: ", stderr);
        if (len)
            fwrite(b, 1, len, stderr);
        fputc('\n', stderr);
    }
    if (getenv("ANF_STATS"))
        fprintf(stderr, "anf: %llu minor collections, %llu words promoted, major heap %u words\n",
                (unsigned long long)st->gc_count, (unsigned long long)st->promoted_words, st->major_hwm);
    return (int)code;
}

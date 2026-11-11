/* Runs a program lowered by AnfLower.v (nanofil/docs/lambda-anf.md, M2):
 * makes the arena of nanofil/anf, calls the module's anf_main, and
 * writes the program's value, a list of bytes (list Byte.byte), to
 * stdout. Byte.byte's 256 constructors take no arguments, so each byte
 * is the immediate (b << 1) | 1, and a cons cell is a block of two
 * fields.
 *
 * ANF_NURSERY (words, default 2^20), ANF_SLAB (words, default 2^28) and
 * ANF_ROOTS (the shadow root stack's words, default 2^24, reserved but
 * not backed until used, as a native stack is) size the arena; the
 * collections and promoted words go to stderr. A root stack too small
 * for a program's recursion ends it with a Fil-C trap, as a native
 * stack overflow does. */
#include <stdio.h>
#include <stdlib.h>
#include "../anf_arena.h"

uint32_t anf_main(uint32_t *arena, struct anf_state *st);

static uint32_t env_words(const char *name, uint32_t dflt)
{
    const char *s = getenv(name);
    return s ? (uint32_t)strtoul(s, NULL, 0) : dflt;
}

int main(void)
{
    uint32_t *arena;
    struct anf_state *st;
    if (anf_arena_init(&arena, &st, env_words("ANF_SLAB", 1U << 28),
                       env_words("ANF_NURSERY", ANF_DEFAULT_NURSERY), env_words("ANF_ROOTS", 1U << 24))) {
        fprintf(stderr, "anf: the arena was not made\n");
        return 2;
    }
    uint32_t v = anf_main(arena, st);
    while (!ANF_IS_IMM(v)) {
        uint32_t idx = ANF_IDX(v);
        if (ANF_HDR_ARITY(arena[idx]) != 2 || !ANF_IS_IMM(arena[idx + 1])) {
            fprintf(stderr, "anf: the value is not a list of bytes\n");
            return 3;
        }
        putchar((int)ANF_IMM_U31(arena[idx + 1]));
        v = arena[idx + 2];
    }
    fflush(stdout);
    fprintf(stderr, "anf: %llu minor collections, %llu words promoted, root_sp %u\n",
            (unsigned long long)st->gc_count, (unsigned long long)st->promoted_words,
            st->root_sp);
    return 0;
}

/* The slow path of the nursery test in modules lowered by AnfLower.v
 * (nanofil/docs/lambda-anf.md, M2 and M3).
 *
 * A stretch of lowered code that allocates `words` words tests
 * young_idx + words > nursery_end once at its head. When it fails, the
 * caller has stored its young index to `st` and pushed its live values
 * onto roots[] (at st + 1); this collects, so the nursery is empty but
 * for what the collection left, and refuses (anf_oom) a stretch that
 * does not fit in an empty nursery. The caller then reads the young
 * index and its values back. */
#include "../anf_arena.h"

void anf_lower_reserve(uint32_t *arena, struct anf_state *st, uint32_t words)
{
    anf_minor_gc(arena, anf_roots(st), st);
    if (words > st->nursery_end - st->young_idx)
        anf_oom();
}

/* Copies the pool of a lowered program's constants (AnfLower.v's
 * pool_item: its number of words, then the words) to the major heap from
 * word 1 on, where the constants' values point; a collection never moves
 * them. The program's entry calls it first, on a fresh arena. */
void anf_lower_pool(uint32_t *arena, struct anf_state *st, const uint32_t *pool)
{
    uint32_t n = pool[0];
    if (st->major_idx != 1U || n > st->major_limit - 1U)
        anf_oom();
    for (uint32_t i = 0U; i < n; i++)
        arena[1U + i] = pool[1U + i];
    st->major_idx = 1U + n;
    if (st->major_idx > st->major_hwm)
        st->major_hwm = st->major_idx;
}

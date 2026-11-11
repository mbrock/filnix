/* The slow path of the nursery test in modules lowered by AnfLower.v
 * (nanofil/docs/lambda-anf.md, M2).
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

/* Reserves `words` words of the major heap for the constants of a
 * lowered program's body, which runs once: they are written there and
 * never move, as no collection evacuates the major heap. Gives the
 * first word's index, or refuses (anf_oom) when the major heap is
 * full. */
uint32_t anf_lower_major(uint32_t *arena, struct anf_state *st, uint32_t words)
{
    (void)arena;
    if (words > st->major_limit - st->major_idx)
        anf_oom();
    uint32_t idx = st->major_idx;
    st->major_idx = idx + words;
    if (st->major_idx > st->major_hwm)
        st->major_hwm = st->major_idx;
    return idx;
}

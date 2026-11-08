# trap / trap reason / Fil-C panic / safety error

**Fil-C** · [InvisiCaps by example](https://fil-c.org/invisicaps_by_example), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

A trap is a Fil-C check failing, which upstream calls a Fil-C panic or safety error (`filc_safety_panic`): the run ends `trap(Reason)`, terminal and uncatchable. Because nothing follows it, a [[check]] is a pure assertion, which is why a check proved never to fail can be deleted without changing behaviour.

- The reasons: `null_capability`, `out_of_bounds`, `misaligned`, `readonly`, `not_a_function`, `argument_size`, `return_size`, `invalid_free`, `double_free`, `too_big`, `out_of_memory`, and `early(Why)` for a [[check_ahead]] whose failure came early. The access check tests null, then bounds, then read-only, then alignment ([cap_access_res]).
- Memory.v's [reason] is shared with [[unchecked]], which adds `alias`, `span`, `half`, `limit` and `ahead(Why)`: the reuse forms' broken trusts, never traps. [res] is a partial result: a value, [RTrap] or [RUnchecked].
- interp.pl's reasons are coarse: past the end, below the start, freed and a function object all trap `out_of_bounds`. The exact native text is compared by progtest and tests/renew-trap.sh.

The subtlety: Campaign 7 does not count every trap as a panic. It counts `too_big` and `out_of_memory` as resource endings ([formal.md, What counts as a panic](../formal.md#what-counts-as-a-panic)).

Defined in [Memory.v](../../rocq/theories/Memory.v) and interp.pl's header.

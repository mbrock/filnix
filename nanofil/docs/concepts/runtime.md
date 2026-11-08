# runtime / runtime axioms

The runtime is what Fil-C does around one thread's program: where a new object goes, what `free` does, and what the collector and other threads may change while the program waits at a [[poll|safepoint]]. The model does not define it; it states it as one page of axioms, `Module Type Runtime` ([Runtime]), each with a native test in `tests/c/prog/axiom-*.c`.

- Ten axioms: [fresh_allocation], [address_space], [non_moving], [free_lifetime] with [safepoint_lifetime], [safepoints], [retention], [free_keeps_ids], [free_checked], [aux_round_trip], [rooting]. Three more [[ready|readiness]] [[obligation|obligations]], [freed_bounds], [ready_kept] and [safepoint_ready], are about the runtime's own bookkeeping and have no native test.
- [InterpRuntime] is interp.pl's runtime: `interp:alloc_base/6` for allocation, `interp:free_res/4` for free, nothing at a safepoint. It proves every axiom, so the module type is consistent and [judge] is closed.
- The [[machine]] runs over any runtime, so every theorem holds of all of them.

The subtlety: the model has one thread and no collector. Another thread's free appears only as the runtime's [safepoint] action; [[retention]] and [non_moving] make a native free between a check and its access equivalent to one at the next safepoint.

Defined in [Runtime.v](../../rocq/theories/Runtime.v); the axioms with their tests and sources are [runtime-axioms.md](../runtime-axioms.md).

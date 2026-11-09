# runtime / runtime axioms

**Fil-C** · [runtime](https://fil-c.org/runtime), [filc_runtime.c](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.c)

The runtime is what Fil-C does around one thread's program, natively libpizlo.so with [[fugc|FUGC]]: where a new object goes, what `free` does, and what the collector may change while the program waits at a [[poll|safepoint]]. The model does not define it; it states it as one page of axioms, `Module Type Runtime` ([Runtime]), each with a native test in `tests/c/prog/axiom-*.c`.

- Ten axioms: [fresh_allocation], [address_space], [non_moving], [free_lifetime], [collector_live], [safepoints], [retention], [free_keeps_ids], [free_checked], [aux_round_trip]. [safepoint_lifetime] and [rooting] were axioms too; they are now lemmas from [collector_live]. Three more [[ready|readiness]] [[obligation|obligations]], [freed_bounds], [ready_kept] and [safepoint_ready], are about the runtime's own bookkeeping and have no native test.
- [InterpRuntime] is interp.pl's runtime: `interp:alloc_base/6` for allocation, `interp:free_res/4` for free, nothing at a safepoint. It proves every axiom, so the module type is consistent and [judge] is closed.
- The [[machine]] runs over any runtime, so every theorem holds of all of them.

The subtlety: the model has one thread and no collector, and its [safepoint] action changes no region ([collector_live]): Fil-C's runtime never frees an object by itself. A signal handler or another thread that frees is the program's code; in the model installing a handler or starting a thread is a call to an external with no contract, which ends the run. Natively, [[retention]] and [non_moving] make another thread's free between a check and its access read retained bytes or trap.

Defined in [Runtime.v](../../rocq/theories/Runtime.v); the axioms with their tests and sources are [runtime-axioms.md](../runtime-axioms.md).

# address space / objects_fit

The address space is where objects may lie: every object within `[0, 2^48]`, native Fil-C's bound (libpas's `PAS_ADDRESS_BITS`). `objects_fit` says this of a memory, and the [[runtime]] axiom `address_space` says it of every memory the runtime is [[ready]] in; the runtime may also refuse an allocation it cannot hold, and the run traps `out_of_memory`.

- Runtime.v: [objects_fit], [address_space]; Machine.v's [mreachable_objects_fit] gives it in every state of a run that starts ready. interp.pl: `interp:address_space/2`, where Next stops at 2^48.
- What it buys: a [[covered-access|covered access]] cannot wrap (needs only 2^64); two addresses of one object are less than 2^63 apart, so a [[renew_hull|hull]] of spans does not straddle the wrap; an address that wrapped below 0, read signed, fails a lower [[half_check]].

The subtlety: Coverage.v needed only 2^64; the hull needed more, and mbrock chose native's 2^48 over a validator change. Whether a valid module's initial data fits is not proved, hence the ready-start hypothesis.

See [runtime-axioms.md, The address space](../runtime-axioms.md#the-address-space) and [rocq.md, Objects end below 2^48](../rocq.md#objects-end-below-248).

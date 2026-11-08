# repeated getter

A repeated getter is a call of a [[getter]] that another call of the same getter dominates in the same activation: a single-definition `let(tmp(D), p, copy, [global(G)])`, G defined in this module with local linkage. The first call has returned, so the repeat takes the fast path: no safepoint, no free, no store. The [[evidence-pass|evidence pass]] lets [[live-fact|live facts]] survive it.

- `ir:repeated_getters/4`, with `ir:local_global/2`; empty in a function with setjmp. Validate.v's [repeated_getters]; Walk.v's [repeated_getter] marks it among the instructions the pass [relies] on.
- Local linkage matters: only then is the getter the one nanofil emits and nobody can interpose it.

The subtlety: the module type still lets the [[runtime]] act before a getter, since it is not `ir:evidence_preserving/1`, so the proofs cover it only through [[spares]]; natively the fast path reaches no safepoint, so it holds there.

See [forward.md, Getters](../forward.md#getters-november-2026).

# spares

**nanofil**

`spares` says that at a safepoint just before an instruction the [[evidence-pass|evidence pass]] keeps facts across, the [[runtime]] changes no [[region]]. Every runtime meets it, so the generic [[soundness]] theorem, once stated under it, no longer takes it as a hypothesis.

- Invariant.v's [spares], over Walk.v's [relies]. The module type lets the runtime act before any instruction that is not `ir:evidence_preserving/1`, yet the pass keeps facts across three such: a pointer store taken with its check, a `check_local`, and a [[repeated-getter|repeated getter]].
- Invariant.v's [spares_any] proves it of every runtime, from the axiom [collector_live]: no region changes at a safepoint. Persistence.v's [safepoint_inv] uses it directly, so [valid_no_unchecked] and the run theorems take no such hypothesis (dropped 2026-11-09), and the interpreter's theorems are plain instances of them.

Why it was a hypothesis: until 2026-11 the runtime's safepoint stood for the thread's signal handlers too, and natively a pointer store whose [[aux]] must be allocated exits to the runtime, which may run a handler that frees the checked object. The store then lands in retained memory, safe by [[retention]] but `unchecked` in the model. mbrock decided (November 2026) to keep it a hypothesis, then (2026-11-09) that a handler is the program's code, not the runtime's: in the model installing one is a call to an external with no contract, which ends the run. What remains is a constraint on verifying handlers: a verified handler must not free an object whose check is in flight, or the theorems weaken to "checked, or freed since its check".

See [rocq.md, The evidence invariant over runs](../rocq.md#the-evidence-invariant-over-runs).

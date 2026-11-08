# spares

`spares` is the one runtime hypothesis of the generic [[soundness]] theorem: at a safepoint just before an instruction the [[evidence-pass|evidence pass]] keeps facts across, the [[runtime]] changes no [[region]].

- Invariant.v's [spares], over Walk.v's [relies]. The module type lets the runtime act before any instruction that is not `ir:evidence_preserving/1`, yet the pass keeps facts across three such: a pointer store taken with its check, a `check_local`, and a [[repeated-getter|repeated getter]].
- The interpreter's runtime changes nothing at a safepoint ([interp_spares]), so [interp_valid_no_unchecked] has no such hypothesis; [valid_no_unchecked] and the run theorems take it.

Why it is not an axiom: it is false natively. A pointer store whose [[aux]] must be allocated exits to the runtime, which may run a signal handler that frees the checked object; the store then lands in retained memory, safe by [[retention]] but `unchecked` in the model. mbrock decided (November 2026) to keep it a hypothesis; weakening the conclusion to "checked, or freed since its check" is left for later.

See [rocq.md, The evidence invariant over runs](../rocq.md#the-evidence-invariant-over-runs).

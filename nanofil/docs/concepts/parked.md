# parked / waiting caller

A waiting caller is a [[frame]] suspended at a call until its callee returns; the configuration keeps them in [c_callers], each with how it will read the result ([pending]). interp.pl has none: its callers wait on Prolog's own stack.

Each run-level invariant says what holds of a waiting caller:

- [parked] (Invariant.v, the [[evidence-invariant|evidence invariant]]): it runs a function of the module, its locals lie above 0, it is not [[doomed]], and it waits just after its call with no fact, since a call ends every [[live-fact|live fact]]; the pass walks the rest of its block from nothing ([walks]).
- [waiting] (Single.v, the [[single-definition|single-definition invariant]]): it is not doomed, waits just after the call that made its callee ([waits]), and holds its [[scope]].

Why no waiting caller is doomed: a doomed frame never calls, so it never becomes one. [call_parked] and [parked_resume] carry a frame into and out of waiting.

See [rocq.md, The evidence invariant over runs](../rocq.md#the-evidence-invariant-over-runs).

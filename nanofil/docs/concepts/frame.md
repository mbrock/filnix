# frame / configuration / config

**nanofil**

A configuration is the whole state of a run in the model: the running frame, the suspended callers (each with how it will read its callee's result), memory, and the [[fuel]] left. A frame is one invocation: its function, its [[temporary|temporaries]], its named locals, whether it is [[doomed]], and its point.

- Semantics.v: [config] with [c_frame], [c_callers], [c_mem], [c_fuel]; [frame] with [fr_fn], [fr_env], [fr_locals], [fr_doomed], [fr_at].
- A frame's [point] is [Snapshot] (a variadic callee about to snapshot its arguments, an allocation), [Enter] (about to run block l, entered from a predecessor or none), or [Exec] (inside block l with instructions left, then a jump).
- interp.pl has no such term: it is big-step, so the frame is its `ctx(...)` term and Env, the callers are Prolog's own stack, and memory and fuel are `s(Mem, Fuel)`. The model makes them explicit so that Campaign 3's invariants can be stated between any two [[step|steps]].

The subtlety: the proofs speak of every frame, not only the running one. The [[single-definition|single-definition invariant]] holds in each [[parked|waiting caller]] too, and a waiting caller is never doomed.

Defined in [Semantics.v](../../rocq/theories/core/Semantics.v); see [rocq.md, Decisions](../rocq.md#decisions).

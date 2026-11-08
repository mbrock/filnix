# outcome

An outcome is how a run ends: a return, `unreachable`, undefined behaviour, a [[trap]], [[unchecked]], or running out of [[fuel]]. interp.pl and the model give the same outcomes term for term, which is what the outcome gate compares.

| interp.pl | Semantics.v |
|---|---|
| `ret(V)`, `rets([X1, X2])`, `ret` | [Ret], [Rets], [RetVoid] |
| `unreachable` | [Unreachable] |
| `ub(Reason)` | [UB] |
| `trap(Reason)` | [Trap] |
| `unchecked(Reason)` | [Unchecked] |
| `out_of_fuel` | [OutOfFuel] |

[outcome] is defined in Semantics.v; Transport.v's [eoutcome] encodes it back as interp.pl's term. interp.pl also has `unknown(asm(M, Xs))` for `asm_fixed`, outside the [[core-subset|core subset]].

`unchecked` is the one a valid module never reaches ([[soundness]], [valid_no_unchecked]). Campaign 7 sorts the others into panics and not: [formal.md, What counts as a panic](../formal.md#what-counts-as-a-panic).

The subtlety: in the model `UB` comes only from an invalid float-to-integer conversion; plain mode's `ub(out_of_bounds(A, Size))` is outside the subset.

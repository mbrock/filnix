# replay / replays

**nanofil**

A [[single-definition|single definition]] replays at a point when its name holds what its own instruction's step made, in some earlier frame that agrees with the current one on the instruction's single-definition operands, and the current memory [[identity|persists]] from the memory that step left, which lay in the [[address-space|address space]].

- [replays] in Single.v. Only [replayable] instructions replay: a `let` that is not an `alloc`, and a [[flight]]. A call or an allocation does not continue with a value, and no reuse rule reads through one.
- There is no table of per-op relations: each reuse form reads what it needs off [inst_step] for the op it trusts. So a check that passed then passes again or traps ([persists_access]), and a flight's capability is its lower donor's.
- Weaker [[scope|scopes]]: [scope_plain] (Ahead.v) asks every single definition but a [[check_ahead]] to replay; [scope_weak] (Doomed.v) lets a doomed check_ahead hold its pointer instead.

On the Prolog side this is the dominance argument of m7.md's round 4, cited in the comments of `ir:same_pointer/3` and `ir:lower_chain/3`: every definition on a chain dominates the point and was computed from its operands' current values.

Defined in [Single.v](../../rocq/theories/soundness/Single.v).

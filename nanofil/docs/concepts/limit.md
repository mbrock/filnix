# limit / check_limit

**nanofil**

`limit(Size)` of a pointer P0 is an opaque class-`l` snapshot of P0's capability and its object's bounds; `check_limit(0, Size, Rights, Align)` of `[P, U]` is exactly a check of P, whose bounds are tested natively against the snapshot U rather than the object's header (plus the free flag, and read-only for a write). A hoisted limit makes a loop's bounds test cheap.

- Validator: `ir:limit_covers/5` asks that U be a single-definition limit of a single-definition P0 and that P reach P0 by a [[lower-chain|lower chain]]; `ir:limit_reads/2` lets nothing but a check_limit read a limit. Validate.v: [limit_covers], [limit_reads].
- Values: interp.pl's `limit(Cap, Size)` is [WLimit] in Values.v. A check_limit whose limit is of another capability is `unchecked(limit)` ([WhyLimit]).
- Guard.v: [lower_chain_sound] gives P the limit's capability, so the instruction checks ([run_guard_checked]).

Why the snapshot is sound: an object's bounds change only when it is freed, which sets the free flag the check also tests.

See [bounds.md](../bounds.md) and [rocq.md, Guards and limits](../rocq.md#guards-and-limits).

# scope

**nanofil**

A frame's scope is the set of [[single-definition|single definitions]] whose [[site]] dominates its point: the names the [[reuse]] rules may read relations off there. The single-definition invariant says every one of them [[replay|replays]].

- Single.v: [point_site] reads the frame's point as a block and index; [scope_with] quantifies over the replayable single definitions whose site dominates it; [scope_holds] asks each to replay. [running] and [waiting] ask it of the running frame (unless [[doomed]]) and of each [[parked|waiting caller]].
- Weaker scopes: [scope_plain] (Ahead.v) excludes `check_ahead` proofs; [scope_weak] (Doomed.v) lets a doomed `check_ahead` hold its pointer instead of a passed check.
- Moving on: [scope_step] across one instruction, [scope_after] for a call's result on return, [scope_mem] for memory.

On the Prolog side there is no term for it: ir.pl reads Once (`ir:single_definitions/3`) and relies on strict-SSA dominance (`ir:definitions_dominate/3`), as the comment on `ir:same_pointer/3` argues.

See [rocq.md, The single-definition invariant](../rocq.md#the-single-definition-invariant).

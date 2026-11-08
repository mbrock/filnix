# step / small step

A step moves a [[frame|configuration]] on by one thing: entering a block (its phis, one unit of [[fuel]]), one instruction, or one jump. [step] answers [Next] with the next configuration, [Done] with an [[outcome]], [Fresh] for an allocation that waits for a base, or [Stuck].

- Semantics.v: [step] for the configuration, reading the [[genv|global environment]], [inst_step] for one instruction, [step_rel] the relation (any [[fresh]] base for an allocation), [reachable] its closure.
- It transcribes interp.pl's big-step `interp:run/5`: `interp:block_outcome/7`, `interp:insts_result/5`, `interp:inst_result/5`, `interp:edge_outcome/7`. Small-step was formal.md's decision, so that invariants can be stated between any two steps.
- [Stuck] is where the interpreter throws or fails: an [[external-call|external call]] other than `free`, an access through an external capability, a temporary read before it is assigned, code outside the [[core-subset|core subset]]. [step_rel] has no step there.

The [[machine]] adds the runtime's steps, allocation and safepoint, on top of these.

Defined in [Semantics.v](../../rocq/theories/Semantics.v).

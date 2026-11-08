# single definition / single-definition invariant

**nanofil**

A single definition is a temporary with exactly one definition in its function: a parameter, a phi or an instruction. The [[reuse]] forms read relations only between such names (a flight and its base, a proof and the pointer it checked, a span test or limit and its pointer), and the single-definition invariant says those relations hold at run time wherever the definition dominates the running point.

- `ir:single_definitions/3` builds the map ir.pl calls Once; Validate.v transcribes it as [single_definitions]. Sites.v gives each one [[site]] ([once_position]) and proves [use_dominated] and [no_use_redefined].
- Single.v states the invariant: in every frame (the running one unless [[doomed]], and each [[parked|waiting caller]]) each single definition in its [[scope]] [[replay|replays]] ([scope_holds], [sinv]). [mreachable_sinv] proves it for any runtime whose free keeps identities; [interp_sinv] proves it for the interpreter with no hypothesis but a ready start.

The subtlety: ir.pl lets a temporary be defined more than once, since `ir:definitions_dominate/3` asks only that one definition dominate each use ([[ssa]]). Names defined twice may change under a reuse rule's feet, so no rule follows one.

See [rocq.md, The single-definition invariant](../rocq.md#the-single-definition-invariant).

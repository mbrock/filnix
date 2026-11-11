# machine / mstep

**nanofil**

The machine of a runtime R, `Machine R`, is what one thread's program sees run under R: Semantics.v's [[step|steps]], plus R's allocations and R's actions at safepoints. [mstep] is its step relation and [mreachable] its runs.

| Step | Is |
|---|---|
| [mstep_next] | a [step] that allocates nothing |
| [mstep_alloc] | an allocation at R's [alloc]; where R refuses there is no step, and the run traps `out_of_memory` |
| [mstep_safepoint] | R's [safepoint] action, only before an instruction where [at_safepoint] holds or before a poll edge ([safepoint_due]) |

[mstep_refines] ties it to the bare semantics: from a [[ready]] state each machine step is a [step_rel] step or a safepoint action, so what is proved of those holds of every run of every runtime.

interp.pl has no counterpart: it is one runtime, built in. ExternalMachine.v extends the machine with labelled [[external-call|external calls]] without changing it.

The subtlety: the runtime acts before the instruction, so the instruction runs on what the runtime left, as native code runs after its pollcheck.

Defined in [Machine.v](../../rocq/theories/soundness/Machine.v); see [rocq.md, Campaign 3: the machine of a runtime](../rocq.md#campaign-3-the-machine-of-a-runtime).

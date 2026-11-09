# state interpretation

**Iris** · iris/program_logic/weakestpre.v (`irisGS_gen`)

The state interpretation is the proposition a language instance ties to the machine's real state. The [[weakest-precondition|WP]] receives it before every step and must give it back for the new state, so it is an invariant of every run; a proof never sees the state itself, only what owning fragments and the interpretation together imply. For heap_lang it is the authoritative [[ghost-state|ghost]] heap, which equals the real heap.

- nanofil's Iris spike, [heap_interp], interprets a memory and a runtime state as a ghost heap of pieces that agrees with the memory, live objects that do not overlap, and a [[ready]] runtime. A [[poll|safepoint]] keeps it with the same ghost heap under the premise that it frees nothing live, from Runtime.v's [non_moving], [aux_round_trip] and [rooting].

See [How Iris works, nanofil's machine in Iris](../iris.md#resources-keyed-by-identity).

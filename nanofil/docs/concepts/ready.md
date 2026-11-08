# ready

**nanofil**

A [[runtime]] is ready in a memory when its own state and that memory agree well enough that its next allocation is [[fresh]]. Readiness is the runtime's invariant: the axioms about allocation and the [[address-space|address space]] are stated only for ready states.

- [ready] is a parameter of [Runtime]; [ready_state] in Machine.v pairs it with the machine's memory. [InterpRuntime]'s says every object lies between 0 and Next, empty if freed, Next is at most 2^48, and nothing at or above Next has been written.
- Every step keeps it ([mreachable_ready]), from [ready_kept], [safepoint_ready] and [fresh_allocation]. Where it holds, [address_space] gives [objects_fit] and [freed_bounds] gives [freed_empty].

The subtlety: "the run starts ready" is a hypothesis of [[soundness]] ([valid_no_unchecked]), not a lemma. A valid module's data has no size limit, and `interp:initial_memory/4` lays it out from 65536 whatever its size, so the initial memory need not be ready. The planned fix starts the heap above the module's data.

See [runtime-axioms.md, Readiness](../runtime-axioms.md#readiness) and [rocq.md, An object past 2^64](../rocq.md#an-object-past-264).

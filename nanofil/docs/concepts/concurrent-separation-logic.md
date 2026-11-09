# concurrent separation logic / CSL / resource invariant

**Iris** · O'Hearn, Resources, Concurrency and Local Reasoning (CONCUR 2004); Brookes, A Semantics for Concurrent Separation Logic (CONCUR 2004)

Concurrent separation logic carries [[separation-logic|ownership]] across threads: threads that own disjoint resources run in parallel without interfering, and a lock guards a resource invariant that the thread taking the lock receives and must restore before releasing it. The decade after it produced a logic per sharing pattern (RGSep, CAP, iCAP, TaDA and more), each with its own soundness proof; [[iris|Iris]] reduced them to ghost state and invariants.

- In Fil-C, other threads and signal handlers are what may free an object under a program, and both are the program's own code: the [[runtime]]'s collector frees nothing at a [[poll|safepoint]] ([collector_live]). nanofil's model has one thread and no handler; a concurrent one would verify the handler or thread as program code, owning only what it was handed.

See [How Iris works, Concurrent separation logic](../iris.md#concurrent-separation-logic).

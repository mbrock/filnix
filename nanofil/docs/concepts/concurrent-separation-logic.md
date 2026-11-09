# concurrent separation logic / CSL / resource invariant

**Iris** · O'Hearn, Resources, Concurrency and Local Reasoning (CONCUR 2004); Brookes, A Semantics for Concurrent Separation Logic (CONCUR 2004)

Concurrent separation logic carries [[separation-logic|ownership]] across threads: threads that own disjoint resources run in parallel without interfering, and a lock guards a resource invariant that the thread taking the lock receives and must restore before releasing it. The decade after it produced a logic per sharing pattern (RGSep, CAP, iCAP, TaDA and more), each with its own soundness proof; [[iris|Iris]] reduced them to ghost state and invariants.

- In Fil-C, other threads and signal handlers are what may free an object under a program. nanofil's model has one thread, and the [[runtime]]'s action at a [[poll|safepoint]] stands for them: it may free any live heap object ([safepoint_lifetime]). A single-threaded proof assumes it frees nothing live ([safepoint_keeps_live]); a concurrent one would replace that premise with ownership the runtime respects.

See [How Iris works, Concurrent separation logic](../iris.md#concurrent-separation-logic).

# Iris invariant

**Iris** · [Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf), POPL 2015; iris/base_logic/lib/invariants.v

An Iris invariant `inv N P` says that P holds, of resources no one owns, between every two steps of the program. It is persistent, so every thread may know it; a thread opens it for one atomic step, takes P out under a [[later-modality|later]], and puts P back before the step ends. Masks record which invariants are open, so none opens twice at once. Since Iris 3 it is defined in the logic from [[ghost-state|ghost state]] and [[update-modality|fancy updates]].

- It is not the global invariant of [never_panics_by_invariant], which is one Rocq predicate on whole configurations that the proof must reestablish at every step. An Iris invariant is a resource that names only what is shared.
- nanofil's planned logic does not need one yet: its model has one thread, and the [[runtime]] at a safepoint is a premise, not a party sharing an invariant.

See [How Iris works, Invariants](../iris.md#invariants).

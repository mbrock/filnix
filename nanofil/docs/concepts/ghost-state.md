# ghost state / own

**Iris** · [Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf), POPL 2015

Ghost state exists only in the proof. `own γ a` owns the piece a of the ghost location γ, where a belongs to a [[camera]]; it is allocated and changed by [[update-modality|updates]], never by the program. It records what the program's memory does not: shares, histories, a protocol's phase, or a whole map that the [[state-interpretation|state interpretation]] ties to the real heap.

- nanofil's ghost heap maps pieces, keyed by [[identity]], to an object's region, a byte or an [[aux]] capability, and the spike's state interpretation, [heap_interp], says it agrees with the memory. The planned [[live]] token is a ghost piece that free consumes; Buffer.v's [holds_buffer] states the same facts about the real memory, as one non-separating fact.

See [How Iris works, Ghost state](../iris.md#ghost-state).

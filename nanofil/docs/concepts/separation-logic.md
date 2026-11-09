# separation logic / separating conjunction / frame rule / points-to

**Iris** · [Reynolds, LICS 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf); O'Hearn, Reynolds and Yang, CSL 2001; Ishtiaq and O'Hearn, POPL 2001

Separation logic is Hoare logic whose assertions describe the part of memory a piece of code owns. `ℓ ↦ v` owns one cell, `P ∗ Q` holds of memory that splits into a part where P holds and a disjoint part where Q holds, and the frame rule lets code proved on what it owns run inside any larger memory, which it leaves alone. Aliasing is ruled out by the assertions, not by side conditions.

- In Iris the frame rule is a lemma about weakest preconditions, `wp_frame_l`, and ∗ is defined on [[camera]] resources rather than heaps.
- nanofil needs it because the facts that keep a [[check]] from failing (this field points to a live 16-byte object) are about objects, and travel with whoever owns them. The planned logic's assertions own pieces keyed by [[identity]]: an object's [[live]] token, its bytes and its [[aux]] slots. [never_panics_by_invariant] is the logic without separation, one invariant naming everything.
- The hand-rolled spike, Sep.v, defines ∗ as a split of a footprint of pieces; the Iris spike uses Iris's.

See [How Iris works, Separation logic](../iris.md#separation-logic).

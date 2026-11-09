# adequacy

**nanofil**

Adequacy is the one theorem that ties a program logic to the [[machine]]: if a program's proof in the logic can be derived, then no state any of its [[run|runs]] reaches fails. It is proved once; after it, proving a program never panics is deriving its proof, with no reasoning about runs.

- [never_panics_by_invariant] in Panics.v is the adequacy of the simplest such logic, one invariant of configurations: if it holds at every admissible start, every [[step]] from it is safe and lands in it for every [[fresh]] base, and a due [[poll|safepoint]] keeps it, then [never_panics] holds. Cycle.v and Buffer.v are proved with it.
- Campaign 3's [valid_no_unchecked] is the adequacy of another fixed logic, the [[validator]]'s facts, for one kind of failure, [[unchecked]].
- [[iris|Iris]] proves adequacy once for every language it is instantiated with, from a [[weakest-precondition|weakest precondition]] of the program. The spike IrisLang.v makes the machine an Iris language in which a configuration that [fails] cannot step, so Iris's adequacy gives [never_panics] directly ([wp_never_panics]) ([How Iris works](../iris.md#adequacy-is-never_panics)).
- In the planned logic, assertions describe owned objects by [[meta]] facts, [[live]] tokens and their cells, and adequacy states that the logic's state interpretation, with Campaign 3's run invariant, holds at every state a run reaches.

See [logic.md, Recommendation](../logic.md#recommendation).

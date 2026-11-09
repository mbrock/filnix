# later modality / step-indexing / step index / Löb induction / löb

**Iris** · Appel and McAllester, TOPLAS 2001; Appel, Melliès, Richards and Vouillon, POPL 2007; Nakano, LICS 2000

Iris's propositions hold or fail at each step index, a budget of program steps still to run, and `▷ P` ("later P") holds at n + 1 when P holds at n. Stored propositions, in invariants or ghost state, come back only under a ▷, and each program step lets a proof remove one. Löb induction, `(▷ P → P) ⊢ P`, proves P while assuming it one step later; loops, recursion and the [[weakest-precondition|weakest precondition]] itself are proved or defined that way.

- In nanofil's Iris spike, a [[poll|safepoint]] is a step from a configuration to itself, so the lifting lemma closes it by Löb induction once, and no program proof mentions safepoints. [[fuel|Fuel]] cannot do this, because a safepoint spends none; for blocks, the machine's fuel ([OutOfFuel]) gives an induction without step-indexing.
- Later credits (Iris 4.0) make the right to remove a ▷ an ownable resource; the spike does not need them.

See [How Iris works, The later modality](../iris.md#the-later-modality).

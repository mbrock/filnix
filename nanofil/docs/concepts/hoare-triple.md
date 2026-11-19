# Hoare triple / Hoare logic / triple

**Iris** · [Hoare 1969](https://dl.acm.org/doi/10.1145/363235.363259); Floyd 1967, Assigning Meanings to Programs

A Hoare triple {P} c {Q} says that if P holds when c starts and c finishes, Q holds when it does. Hoare logic gives one rule per construct: assignment substitutes into the postcondition, sequencing chains triples, a loop needs an invariant each iteration keeps. It is partial correctness: a run that never finishes satisfies every triple.

- Iris writes a triple `{{{ P }}} e {{{ RET v; Q }}}` and defines it from the [[weakest-precondition|weakest precondition]], as `□ ∀ Φ, P -∗ ▷ (Q -∗ Φ v) -∗ WP e {{ Φ }}`: for any continuation Φ, owning P and the promise that Q gives Φ, e is safe and ends in Φ.
- Hoare logic breaks on pointers, because an assignment through one pointer may change what another names; [[separation-logic|separation logic]] is the fix.
- Nanofil's early single-program proofs used Floyd's method. The rule [never_panics_by_invariant] checks that each step preserves an invariant on configurations.

See [How Iris works, Hoare logic](../iris.md#hoare-logic).

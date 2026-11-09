# magic wand / wand / separating implication

**Iris** · [Reynolds, LICS 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf)

The magic wand `P -∗ Q` holds of resources that, joined with any disjoint resources where P holds, give resources where Q holds. It is a structure with a hole that P fills: a function's precondition is a wand to its weakest precondition, and a structure that lends out a part owns `part ∗ (part -∗ whole)`.

- Iris's [[hoare-triple|triples]] and the continuation style of its specifications are wands: `lst p xs -∗ cont -∗ WP …` in the spike's [sum_spec].
- Hello's quotearg returns a buffer that stays valid only until the next call with its slot; its specification lends it out, `string ret ∗ (string ret -∗ slots)`, which a first-order logic would have to encode. Campaign 4's libc contracts frame by hand instead: [local_effect] says a call changes only what its writable roots reach.

See [How Iris works, Separation logic](../iris.md#separation-logic).

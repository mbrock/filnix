# camera / resource algebra / RA / CMRA / frame-preserving update

**Iris** · [Higher-Order Ghost State](https://iris-project.org/pdfs/2016-icfp-iris2-final.pdf), ICFP 2016; iris/algebra

A camera is the kind of resource Iris's propositions are about: a set with a composition ⋅ of two pieces, a validity ✓ saying which compositions are possible, and a step-indexed equality. Owning two pieces is owning their composition. A frame-preserving update `a ~~> a'` changes a piece to another that stays valid with anything another party could own. Choosing a camera is choosing what can be owned and how it may change.

- Common ones: Excl (exclusive), fractions (shares in (0, 1]), Agree (a value that never changes), and the authoritative camera (● the whole, ◯ fragments of it), on which Iris's heap, gen_heap, is built.
- The step-indexed equality is what lets ghost state hold propositions (higher-order ghost state), the basis of [[iris-invariant|invariants]].
- nanofil's ghost heap in the spike is a gen_heap from pieces keyed by [[identity]] to values; a planned [[meta]] fact is a persistent ghost_map element, stable because Runtime.v never reuses an identity ([fresh_allocation], [free_keeps_ids]).

See [How Iris works, Ghost state](../iris.md#ghost-state).

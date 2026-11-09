# Iris Proof Mode / IPM / MoSeL / proof mode

**Iris** · [Krebbers, Timany and Birkedal, POPL 2017](https://iris-project.org/pdfs/2017-popl-proofmode-final.pdf); [MoSeL](https://iris-project.org/pdfs/2018-icfp-mosel-final.pdf), ICFP 2018

The Iris Proof Mode is a set of Rocq tactics that give separation-logic goals their own context: hypotheses named by strings, a persistent zone that can be used again and a spatial zone whose hypotheses tactics consume. `iIntros`, `iDestruct "H" as "[H1 H2]"`, `iFrame`, `iSplitL`, `iMod`, `iNext` and `iLöb` do the splitting, framing and modal reasoning that would otherwise be lemma chains; typeclasses make them extensible.

- It is where Iris most clearly beats nanofil's hand-rolled spike, whose framing is done by hand: reassociating stars and dropping walked nodes. The single-invariant proofs ([never_panics_by_invariant]) avoid framing by naming everything in one assertion.

See [How Iris works, The proof mode](../iris.md#the-proof-mode).

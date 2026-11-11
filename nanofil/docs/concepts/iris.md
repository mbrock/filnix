# Iris

**Iris** · [iris-project.org](https://iris-project.org/); [Iris from the Ground Up](https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf), JFP 2018

Iris is a higher-order [[concurrent-separation-logic|concurrent separation logic]] framework in Rocq. Its propositions describe owned resources, may quantify over propositions, and are shared through [[iris-invariant|invariants]]; user-defined [[ghost-state|ghost state]] expresses protocols. A language joins it by giving its step relation, and [[adequacy]] turns a [[weakest-precondition|weakest precondition]] proved in the logic into a fact about every run.

- nanofil's machine is an Iris language in [Language.v](../../rocq/theories/logic/Language.v), built so that a failing frame has no step; Iris's adequacy then proves [never_panics] itself ([wp_never_panics]). logic.md recommends Iris for the never_panics campaign.

See [How Iris works](../iris.md).

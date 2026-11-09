# update modality / basic update / fancy update / mask

**Iris** · [The Essence of Higher-Order Concurrent Separation Logic](https://iris-project.org/pdfs/2017-esop-iris3-final.pdf), ESOP 2017

An update modality says a proposition holds after a change the proof makes on its own, with no program step. The basic update `|==> P` changes [[ghost-state|ghost state]] by frame-preserving updates and allocates new ghost locations. The fancy update `|={E1,E2}=> P` may also open and close [[iris-invariant|invariants]], from the mask E1 of closed invariants to E2; `P ={E}=∗ Q` is `P -∗ |={E}=> Q`.

- In nanofil's Iris spike, an allocation's step gives the new object's pieces by a basic update (gen_heap's allocation) after the runtime picks a [[fresh]] base ([fresh_allocation]), and a store changes the stored pieces' values by another.

See [How Iris works, Update modalities](../iris.md#update-modalities).

# persistent proposition / persistence modality / persistent

**Iris** · iris/bi

A persistent proposition is knowledge rather than ownership: it owns nothing exclusive, so it can be copied, `□ P` giving `□ P ∗ □ P`, and kept after it is used. Pure facts `⌜φ⌝`, [[iris-invariant|invariants]], a cell that never changes again (`ℓ ↦□ v`) and specifications of functions are persistent; `ℓ ↦ v` is not.

- nanofil's planned [[meta]] fact is persistent: nothing after an allocation changes what was allocated, and Runtime.v never reuses an identity ([fresh_allocation], [free_keeps_ids]), so the fact that b was allocated with n bytes stays true after b is freed. The [[live]] token is the part that is not.

See [How Iris works, Propositions are resources](../iris.md#propositions-are-resources).

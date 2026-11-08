# guard chain

**nanofil**

A pointer's guard chain lists its bases with the offset of its address from each: P itself at `i(0, 0)`, then each base B reached through single-definition `add`, `sub` and `copy` [[flight|flights]] whose lower donor is their address operand, with an interval for P's address minus B's, modulo 2^64. P has the capability of every base on its chain.

- `ir:guard_chain/3` (at most 64 steps), offsets from `ir:offset_interval/8`. Readers: `ir:guard_covers/5` ([[renew_if]]), [[pointer-distance|pointer distance]] (`ir:pointer_distance/4`, `ir:same_pointer/3`) through an [[exact-base|exact base]] `i(K, K)`, `ir:raise_need/6` ([[need]]). Validate.v: [guard_chain], [pointer_distance].
- Chain.v: [guard_chain_sound] (each stable element holds of the pointer) and [pointer_distance_sound] (two pointers D apart share a capability, their addresses D apart modulo 2^64).

The subtlety: offsets are exact only modulo 2^64, so readers that need a true signed distance accept only [[near-offset|near offsets]]. A practical one: Chain.v rewrites `guard_chain` by equations and never unfolds it in a hypothesis, or `Qed` takes minutes.

See [rocq.md, Reading single definitions](../rocq.md#reading-single-definitions).

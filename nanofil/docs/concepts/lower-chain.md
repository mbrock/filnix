# lower chain

A lower chain from P to B says P carries B's [[capability]]: P is B, or a single-definition [[flight]] whose lower donor has B's lower, whatever its address.

- `ir:lower_chain/3`, at most 64 steps; `ir:limit_covers/5` uses it to accept a [[limit|check_limit]]. Validate.v transcribes [lower_chain].
- Guard.v's [lower_chain_sound]: each step is a flight whose capability is its lower donor's, so at any point the chain's definitions dominate, P has B's current capability.

It differs from a [[guard-chain|guard chain]], which follows only `add`, `sub` and `copy` flights whose lower donor is their address operand, and tracks the offset as well. A lower chain ignores addresses entirely, which is all a limit needs: the snapshot fixes the bounds, so only the identity must match.

See [rocq.md, Guards and limits](../rocq.md#guards-and-limits).

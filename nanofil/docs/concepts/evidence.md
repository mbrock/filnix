# evidence

Evidence is whatever discharges an access's requirement, the authority over the bytes it touches. Today it is a [[check]] immediately before the access, an earlier heap check whose [[live-fact|live fact]] still holds, or a [[reuse]] form's trust: for [[renew]] a dominating check, for [[renew_if]] a [[guard]]'s [[span_test|span test]].

- The validator's fact for it is `live(Q, P, Lo, Hi, Rights, Align)` (`ir:checked_insts/5`); Rocq's is [fact], with its meaning [fact_holds].
- The [[evidence-pass|evidence pass]] tracks it, and the [[evidence-invariant|evidence invariant]] proves it true along runs.

[campaign.md](../campaign.md) separates requirement, evidence and implementation: an optimizer may choose cheaper evidence, never weaker.

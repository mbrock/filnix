# evidence pass

The evidence pass is the validator's forward walk over a checked function: it tracks [[live-fact|live facts]] and accepts each raw access only where its own check, a live fact or a reuse rule covers it. It visits the blocks once, in order; a block's [[exit-facts|entry facts]] are the meet over its incoming edges, with nothing carried over a poll edge or from a block not yet visited.

- ir.pl: `ir:stage_func/6` drives it, with `ir:checked_insts/5`, `ir:checked_inst_rest/7` and `ir:evidence_after/3`. Validate.v: [evidence_pass], [checked_inst_rest], [evidence_meet].
- It keeps facts across every `ir:evidence_preserving/1` instruction and drops all of them at any other, but for three: a pointer store taken with its check, a `check_local`, and a [[repeated-getter|repeated getter]].

That what it computes holds at run time is the [[evidence-invariant|evidence invariant]], proved in Evidence.v, Walk.v, Invariant.v and Persistence.v; the three exceptions above are why the generic theorem takes [[spares]].

See [m7.md, Across edges (round 2)](../m7.md#across-edges-round-2) and [rocq.md, The evidence invariant over runs](../rocq.md#the-evidence-invariant-over-runs).

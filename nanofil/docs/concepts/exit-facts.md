# exit facts / entry facts

**nanofil**

A block's exit facts are what a validator pass knows at its jump; its entry facts are what it knows before its phis. Two passes keep them, over the same edge rule: entry facts are the meet over incoming edges, nothing comes over a poll edge, and an edge from a block the pass has not yet reached carries nothing.

- The [[evidence-pass|evidence pass]], forward: exit facts are [[live-fact|live facts]] at the block's end, kept per label (`ir:stage_func/6`). Walk.v's [pass_exits] reads them back; Invariant.v's [point_ok] asks a block's entry, from a predecessor by an unpolled edge, to see that predecessor's exit facts hold.
- The [[need]] analysis, backward: exit needs are the meet over a block's own edges of its targets' entry needs, keeping the least (`ir:ahead_edge/5`, `ir:ahead_meet/2`). Ahead.v's [block_exit] and [ahead_entry].

The subtlety: the meet over no edges is empty, so a block reached first by a back edge, or a function's entry, starts with no facts at all.

See [schedule.md, Validator rule](../schedule.md#validator-rule-irpl-independent-of-the-pass).

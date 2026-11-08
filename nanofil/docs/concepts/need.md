# need / needs

**nanofil** · the check scheduler, `filc-optimize-checks` ([FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp))

A need is the validator's backward fact for [[check_ahead]]: need(B) = H at a point says every path from it reaches a raw heap access through a pointer of which B is an [[exact-base|exact base]], whose bytes reach B + H, and reaches it first: before any instruction that is not [[ahead-transparent]], any poll edge, edge back or end, and before B is redefined.

- ir.pl computes needs in one backward sweep over the blocks, last first: `ir:ahead_justified/3` with `ir:ahead_block/6`, `ir:ahead_edge/5`, `ir:raise_need/6` and `ir:ahead_meet/2`. A block's [[exit-facts|exit needs]] are the meet over its edges, keeping the least H; a plain edge to a later block carries that block's entry needs, any other edge none.
- Ahead.v states them as functions of the point, [block_exit] and [facts_from], and proves the sweep computes them ([ahead_entry], [ahead_accepted]). Doomed.v carries them forward along a doomed run ([need_at]); the access that meets one fails ([need_access_fails]).

The subtlety: offsets along a [[guard-chain|guard chain]] are exact only modulo 2^64, so a need counts only [[near-offset|near offsets]].

See [schedule.md, Validator rule](../schedule.md#validator-rule-irpl-independent-of-the-pass) and [rocq.md, Facts ahead](../rocq.md#facts-ahead).

# dominance / dominates / dominator / dominator tree / dominator interval / immediate dominator / idom / reverse postorder / preorder interval

Block A dominates block B when every path from the entry to B passes through A. The validator decides it with the dominator tree's preorder intervals: each label gets the numbers of its subtree, and A dominates B when B's number lies in A's interval.

- cfg.pl: `cfg:reverse_postorder/6` orders the blocks, `cfg:cfg_idoms/2` finds each block's immediate dominator (idom), its parent in the tree, by Cooper, Harvey and Kennedy's fixpoint, `cfg:dom_intervals/3`, `cfg:dominates_by_interval/3`; Cfg.v transcribes them as [cfg_idoms], [dom_intervals], [dominates_by_interval] and [block_intervals].
- Dominance.v proves the computed tree sound: [dom_entry] and [dom_closed] (a run enters only blocks with an interval), [dom_edge] (dominance survives an edge), [dom_meet] (what dominates every reachable predecessor dominates the block, from [idoms_nca]), [dom_antisym], [dominates_trans].
- Readers: `ir:definitions_dominate/3` ([[ssa]]), `ir:site_dominates/4` ([[site]]), [[repeated-getter|repeated getters]], and every reuse rule through [[single-definition|single definitions]].

The subtlety: soundness only. The proof never shows the idoms are the true immediate dominators, and Cfg.v's fuel bounds stay unproved; a bound too small makes the validator reject a function, never accept a wrong one. Labels must be unique ([no_dups]).

See [rocq.md, Dominance](../rocq.md#dominance).

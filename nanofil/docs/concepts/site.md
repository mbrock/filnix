# site / definition site

A site is where a temporary is defined: `param` for a parameter, or `at(L, I)` for index I of block L, with phis at index -1. A site dominates a position when it comes before it on every path from the entry: the same block at an earlier index, or a block that strictly [[dominance|dominates]] it.

- ir.pl: `ir:block_sites//1` records every definition's site, `ir:site_dominates/4` orders them, and `ir:definitions_dominate/3` asks a dominating one for each use. Validate.v: [site] ([SParam], [SAt]), [temp_sites], [site_dominates].
- Sites.v joins these sites with the list `ir:single_definitions/3` filters, through one list [def_positions]; Single.v's [point_site] reads a frame's point as a site, so the invariant compares like with like.
- A phi's operand is used at the end of its predecessor, not at the phi.

The subtlety: the proofs use the validator's own sites rather than a second notion of position, so `site_dominates` is exactly the order the run-level invariants are stated in.

See [rocq.md, Where a name is defined](../rocq.md#where-a-name-is-defined) and [Sites.v](../../rocq/theories/Sites.v).

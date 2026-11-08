# campaign

**nanofil**

A campaign is one numbered stage of nanofil's formal plan in formal.md, from Campaign 0 (measure which checks survive) to Campaign 7 (prove one program never panics). Each ends with a note in docs/ saying what it found.

| Campaign | Goal | Note |
|---|---|---|
| 0 | measure the residual checks | [residual.md](../residual.md) |
| 1 | the core model in Rocq, agreeing with the [[interpreter]] | [rocq.md](../rocq.md) |
| 2 | the [[runtime]] as axioms | [runtime-axioms.md](../runtime-axioms.md) |
| 3 | [[soundness|soundness of checking]], [valid_no_unchecked] | [rocq.md](../rocq.md#campaign-3-the-machine-of-a-runtime) |
| 4 | observations, refinement, libc [[external-call|contracts]] | [libc-contracts.md](../libc-contracts.md) |
| 5 | static discharge by certificate | not started |
| 6 | integration with Filnix | not started |
| 7 | trap-freedom of one pinned program | [trap-census.md](../trap-census.md) |

The word has two other meanings nearby. [campaign.md](../campaign.md) is "the campaign": nanofil's foundation as an executable account of Fil-C's capability semantics, which formal.md extends. And "the full campaign" is the opt-in Rocq check with every [[mutant]]. Filnix's port campaign is unrelated.

See [formal.md, The campaigns at a glance](../formal.md#the-campaigns-at-a-glance).

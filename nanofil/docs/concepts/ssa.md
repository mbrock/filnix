# strict SSA / SSA

**nanofil**

Strict SSA is the form of a function in which every use of a temporary is [[dominance|dominated]] by a definition of it. nanofil uses the name in two strengths: the middle end's `promote:strict_ssa/3` also asks that each temporary have exactly one definition, while the validator's `ir:definitions_dominate/3` allows several and asks only that one dominate each use.

- Checked IR need only pass the validator's form (tests/fixtures/memory.ir defines a temporary twice). The [[reuse]] rules restrict themselves to [[single-definition|single definitions]], which have both properties.
- Rocq: [definitions_dominate] in Validate.v, whose header calls it strict SSA; Sites.v's [use_dominated] reads it back: a single-definition name a reachable instruction uses is defined at a [[site]] that dominates the use.
- Phi operands are used at the end of their predecessor; unreachable blocks are not checked.

Why it matters: with strict SSA, a dominating single definition holds the value it computed from its operands' current values, which is what lets the validator reason about pointers by name.

See ir.pl's comment on `ir:definitions_dominate/3` and [guide.md, The IR is the contract](../guide.md#the-ir-is-the-contract).

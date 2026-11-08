# phi

A phi `phi(tmp(D), K, [Pred-Value])` gives D the value paired with the block control came from. A block's phis run together on entry, each reading its operand as it stood at the end of the predecessor.

- Syntax.v's [phi]; Semantics.v's [phis_env], applied when a frame at [Enter] names the block it came from; interp.pl does the same in `interp:block_outcome/7`.
- The validator treats a phi's operand as used at the end of its predecessor, and its own [[site]] as index -1 of its block (`ir:block_sites//1`). Phi destinations end the [[live-fact|live facts]] and [[need|needs]] that name them.
- On a poll edge the pollcheck runs after the phis' copies.

The subtlety: a phi counts as a definition, so its destination can be a [[single-definition|single definition]] (`ir:single_definitions/3`), yet it is not [replayable]: its value depends on the edge taken, and no reuse rule reads a relation through it.

Natively a phi has a [[shadow]] slot for the parallel copy.

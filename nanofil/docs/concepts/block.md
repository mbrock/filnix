# block / basic block / label

**nanofil**

A block is a labelled straight line of a function: [[phi|phis]], then instructions, then one jump (`goto`, `branch`, `ret`, `rets`, `ret`, `unreachable`). The first block is the entry and has no phis; its label is the name edges use.

- ir.pl: `block(Label, Phis, Insts, Jump)`; Syntax.v: [block] with [b_label], [b_phis], [b_insts], [b_jump]; Semantics.v's [find_block].
- A jump target may be `poll(L)`, a [[poll]] edge. The control-flow graph is `cfg:func_cfg/2` ([func_cfg]).
- Entering a block costs one unit of [[fuel]] (`interp:block_outcome/7`, [step] at [Enter]), so the model's `OutOfFuel` comes where the interpreter's does.

The subtlety: labels must be unique ([no_dups], checked by [valid_func]). The successor map keeps the last block of a label while the machine runs the first, so with a duplicate the proofs about [[dominance]] would speak of a different graph from the one that runs.

Defined in ir.pl's header and [Syntax.v](../../rocq/theories/core/Syntax.v).

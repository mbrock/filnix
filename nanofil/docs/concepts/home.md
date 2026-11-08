# home

A home is the 8-byte frame word that holds a [[temporary]], a [[phi]]'s [[shadow]] or a pointer's address word in the stack-homed stream amd64_regs starts from ([guide.md, 12. Register homes](../guide.md#12-register-homes-and-their-checker-amd64_regspl-amd64_regs_checkpl)). Scalar homes are `w` or `l` only; float temporaries are kept out of them.

Under `--registers=temps|pointers` a home may be mapped to a register (`amd64_regs:regs_asm/6`); the register checker refuses a home that overlaps a [[root]]. Homes are a backend matter, with no counterpart in the formal model.

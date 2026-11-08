# translation validation

Translation validation checks each transformation's result rather than proving the transformation once: nanofil's register checker, the check passes' `*_refines/2`, and the interpreter refinement of `difftest -O` (`amd64_regs_check:check_regs/5`, `opt:refines/2`, [[refines]]). A wrong pass then makes a compile fail rather than produce a wrong output, as far as the checker is right.

The [[validator]] plays the same part for check passes: every producer of checked IR must get past it, and [[soundness]] makes that checker proved. At formal.md's horizon, filcc's own output would be validated the same way.

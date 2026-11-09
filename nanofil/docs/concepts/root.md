# root / Pizderson frame

**Fil-C** · [safepoints, Pizderson frames](https://fil-c.org/safepoints#pizderson), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

A root is a frame word the collector scans for live capabilities: an entry of the Pizderson frame's `lowers[]` (the record each function keeps on the stack: a parent link, an [[origin]] and the lowers), a local's stack [[aux]], or a jmpbuf root (`filc_abi:lower_function/5`, `amd64_regs_check:valid_map/3`). Every live [[lower]] is in one at every [[poll|safepoint]], so registers never hold the only copy.

The model has no roots: the [[runtime]] lemma [rooting], from the axiom [collector_live], says instead that a safepoint reclaims no [[identity]] the program can name.

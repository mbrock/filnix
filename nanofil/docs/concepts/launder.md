# launder

**Fil-C** · [GIMSO, inttoptr](https://fil-c.org/gimso#inttoptr), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp)

Laundering gives an integer converted back to a pointer the [[capability]] of the pointer it came from, as Fil-C does when its analysis can follow the integer: through arithmetic, promotable local variables and phis, never through memory or a call, and only from one pointer (`launder:launder_func/4`, [m4.md](../m4.md), *Pointer-as-int laundering*). Otherwise the pointer gets no capability and dereferencing it traps.

Upstream it is FilPizlonator's pointer-as-int laundering: an abstract interpreter over the integer SSA values, in which each `ptrtoint` starts as its pointer, loads and calls as nothing, and a value reached from two pointers as conflicting.

Laundering rewrites the IR before checking; the model sees only its result. An unlaundered `itop` yields a pointer with [CNone] ([Itop]). launder.pl's capability [[shadow]] is a different use of the word.

# launder

Laundering gives an integer converted back to a pointer the [[capability]] of the pointer it came from, as Fil-C does when its analysis can follow the integer: through arithmetic, promotable local variables and phis, never through memory or a call, and only from one pointer (`launder:launder_func/4`, [m4.md](../m4.md), *Pointer-as-int laundering*). Otherwise the pointer gets no capability and dereferencing it traps.

Laundering rewrites the IR before checking; the model sees only its result. An unlaundered `itop` yields a pointer with [CNone] ([Itop]). launder.pl's capability [[shadow]] is a different use of the word.

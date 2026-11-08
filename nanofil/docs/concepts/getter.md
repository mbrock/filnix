# getter

**Fil-C** · [runtime, linking](https://fil-c.org/runtime#linking), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp)

A getter is the function that returns a global's or function's address with its [[capability]], initializing it on first use. Upstream every symbol is renamed `pizlonated_` plus its name, and that symbol is its getter, returning a [[flight-pointer|flight pointer]]; the program checks the result like any pointer. In IR a getter call is `let(tmp(D), p, copy, [global(G)])`; calling one is a [[poll|safepoint]] (`filc_amd64:object_getter//2`), so it ends every [[live-fact|live fact]], except a [[repeated-getter|repeated getter]].

The model has no getter call: a [Global] operand reads the symbol's pointer from the [[genv|global environment]]'s [ge_globals], or an external capability for a symbol the module does not define.

# alloc

**Fil-C** · [GIMSO](https://fil-c.org/gimso), [compiler](https://fil-c.org/compiler), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp)

An allocation: `let(D, p, alloc(Align), [Size])` makes a fresh, zeroed heap object of Size bytes and yields a pointer to it with its [[capability]]. The frontend gives every C local one; promote and local_storage remove most of them under `-O` (`promote:promote_module/2`, `local_storage.pl`).

- Rocq: the op [Alloc], whose request [heap_req] the [[runtime]]'s [alloc] places at a [[fresh]] base. A size over 2^48 - 1 traps `too_big` before anything is allocated (`interp:alloc_res/6`, [max_allocation_size]); where the runtime cannot hold the object, the run traps `out_of_memory`.
- Upstream every alloca becomes a FUGC allocation too, and FilPizlonator's escape analysis puts those that do not escape back on the stack; promote and local_storage are nanofil's counterpart.
- An allocation is a [[poll|safepoint]], so it ends every [[live-fact|live fact]].

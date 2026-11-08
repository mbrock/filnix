# interpreter

**nanofil**

The interpreter is interp.pl, nanofil's executable meaning of the IR: a relation from a module, a function, arguments and [[fuel]] to an [[outcome]], with CLP(Z) integers so that it runs in every direction. The Rocq model transcribes it, and the outcome gate checks that the two agree on every run line of the corpus.

- Entry points: `interp:run/5`, or `interp:module_prepared/2` once and `interp:run_prepared/5` many times. The tests also compare it with the native code nanofil and clang emit (difftest, progtest).
- Rocq: Semantics.v transcribes its steps, small-step where interp.pl is big-step; Run.v's `Driver InterpRuntime` ([Driver], [InterpRuntime]) runs them with the interpreter's allocator and free. "The interpreter's runtime" means [InterpRuntime], which proves every [[runtime]] axiom.

The subtlety: it is the deterministic explicit-free subset, not a GC simulator: no reclamation, no concurrent or signal-handler frees, no free singleton. It has been both more permissive than native (an object past 2^64, now refused) and stricter (a freed snapshot's renew, now a trap); each was fixed toward native.

See [guide.md, 13. Running it](../guide.md#13-running-it-interppl) and interp.pl's header.

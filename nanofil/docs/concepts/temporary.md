# temporary / temp

A temporary is a function-local IR name, `tmp(N)`, holding one [[word]] of one [[class]]. Parameters, phis and instructions define temporaries; operands read them. Names are ground terms, compared only for equality: no logic variable appears in IR.

- ir.pl's header ("Temps are ground names"); Syntax.v's value [Tmp]. At run time Semantics.v's environment [env] maps each temporary assigned so far to its word, as interp.pl's Env does; Term.v's [lookup] and [put] read and write it.
- [[proof|Proofs]] (classes `a` and `f`) are temporaries too, but never parameters, phis, call arguments or stored values.
- Named locals are a separate namespace: objects declared by `local_alloc`, not temporaries.

The subtlety: a temporary may have more than one definition (`ir:definitions_dominate/3` asks only that one dominate each use), so "the value of `tmp(N)`" depends on where you stand; the reuse rules follow only [[single-definition|single definitions]]. Reading a temporary before it is assigned is [Stuck] in the model, an instantiation error in interp.pl.

See [guide.md, The IR is the contract](../guide.md#the-ir-is-the-contract).

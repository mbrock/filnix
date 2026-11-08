# external call / contract

**nanofil** · libc is Fil-C code too, and only the runtime calls native code ([runtime](https://fil-c.org/runtime))

An external call is a call to a symbol the module does not define, in practice libc. The core model sends only `free` to the [[runtime]] and is stuck at every other. A contract is Campaign 4's trusted description of one external function: its ABI, the caller's premises, the roots it may write, what it may release or allocate, its observations and its endings.

- Core: Semantics.v's [external_call] and [free_name], which run the [[genv|global environment]]'s [ge_free]; interp.pl's external `call(void, global(free), [arg(p, P)])`, which module-defined functions take precedence over.
- ExternalCalls.v: [contract], [effects], [invoke], [puts_contract]. ExternalMachine.v: [external_site] (direct calls only, never in a [[doomed]] frame), [no_violation], and [run_preserve], which carries readiness, identities and both invariants through labelled runs. The extracted driver is unchanged.

The subtlety: a failed premise is an unmet caller [[obligation]], a `ContractViolation` ending, not a claim that native libc traps. Within its contract a call may return, exit or exhaust resources, but never give [[unchecked]] or a capability panic.

The table of contracts is [libc-contracts.md](../libc-contracts.md); see [formal.md, Campaign 4, milestone 1](../formal.md#campaign-4-milestone-1-a-standalone-contract-boundary).

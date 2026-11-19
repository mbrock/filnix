# obligation / realization obligation

**nanofil**

An obligation is something a proof leaves to be shown or trusted elsewhere. A realization obligation says that native code behaves as a logical model specifies.

The formal documents use the word in four senses:

- **Readiness obligations** of the [[runtime]] module type: [freed_bounds], [ready_kept] and [safepoint_ready], about the runtime's own bookkeeping, with no native test; [InterpRuntime] proves them.
- **Caller obligations**: a premise of an [[external-call|external call]]'s contract. A failed one is a `ContractViolation`, not a claim that the native callee traps.
- **Realization obligations**: the [runtime boundary](../zsys.md) relies on libpizlo honoring the contracts for calls that leave the compiled image.
- **Proof obligations** of campaign.md: [[soundness|soundness of checking]], transformation correctness and implementation correctness, kept apart; Campaign 4 gives each pass and `--checks` mode a refinement obligation, against `opt:refines/2` restated as trace inclusion.

See [formal.md, The claims, kept apart](../formal.md#the-claims-kept-apart).

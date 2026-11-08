# obligation / realization obligation

An obligation is something a proof leaves to be shown or trusted elsewhere, named rather than assumed away. A realization obligation is the trusted claim that native code realizes a logical model: that pinned libc's FILE, buffering and dispatch behave as Stdio.v's protocol and Libio.v's memory view say.

The formal documents use the word in four senses:

- **Readiness obligations** of the [[runtime]] module type: [freed_bounds], [ready_kept] and [safepoint_ready], about the runtime's own bookkeeping, with no native test; [InterpRuntime] proves them.
- **Caller obligations**: a premise of an [[external-call|external call]]'s contract. A failed one is a `ContractViolation`, not a promise that native libc traps ([libc-contracts.md, Traps](../libc-contracts.md#traps-admissible-inputs-versus-violations)).
- **Realization obligations**: Stdio.v's [stream_accounting] proves the protocol consistent, not that native stdio follows it; native coverage of each contract stays trusted.
- **Proof obligations** of campaign.md: [[soundness|soundness of checking]], transformation correctness and implementation correctness, kept apart; Campaign 4 gives each pass and `--checks` mode a refinement obligation, against `opt:refines/2` restated as trace inclusion.

See [formal.md, The claims, kept apart](../formal.md#the-claims-kept-apart).

# identity / object identity / persists

An object's identity is its base, the number its [[capability|capabilities]] name; it outlives the object's bounds, so a freed object keeps its identity. One memory persists from another when every object of the first is in the second as it was, or freed: no identity is lost, moved or given to a new object.

- Identity.v: [ids] (every object is still an object) and [persists] (as it was, or freed). [persists_access]: a check that passed in m passes again in a memory that persists from m, or traps out of bounds. That is what lets a [[reuse]] form trust an earlier check.
- [mreachable_persists]: every [[run]] that starts [[ready]] persists, from the runtime axioms [free_keeps_ids] (free reclaims nothing), [rooting] (a safepoint reclaims nothing the program can name) and [fresh] allocation.
- interp.pl gets it by construction: Next never reuses an address, and free keeps the region.

The subtlety: natively a freed object's address may be a new object's after a collection. Model and native agree on whether each access through a capability the program holds traps, not on its address bits.

See [rocq.md, Identities persist](../rocq.md#identities-persist) and [runtime-axioms.md, How the model uses them](../runtime-axioms.md#how-the-model-uses-them).

# live / live token

**nanofil** · proposed, not yet in the model; Fil-C's free flag is what it tracks ([runtime](https://fil-c.org/runtime))

A live token, `live b`, is permission to rely on the object of [[identity]] b not being freed. It is the temporal half of a [[check]]: the bounds come from b's [[meta]] fact, and the free flag passes as long as the token is held. Free consumes it, so whoever frees an object must own it, and an object no one else owns cannot be freed behind the owner's back. For a heap object it is exclusive, or split into fractions for readers; for global data, which is never freed, it is persistent.

- The [[runtime]] is the one other party that could free: Runtime.v lets a [[poll|safepoint]] free a live heap object ([safepoint_lifetime]), standing for another thread or a handler. A program that holds its own tokens across a safepoint needs a runtime that does not, the premise Buffer.v states as [safepoint_keeps_live] and Hi.v as `stdio_stable`.
- A flag-only [[renew]] asks for nothing but this token.

See [logic.md, Where the proposal is right](../logic.md#where-the-proposal-is-right).

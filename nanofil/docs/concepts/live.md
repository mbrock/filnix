# live / live token

**nanofil** · proposed, not yet in the model; Fil-C's free flag is what it tracks ([runtime](https://fil-c.org/runtime))

A live token, `live b`, is permission to rely on the object of [[identity]] b not being freed. It is the temporal half of a [[check]]: the bounds come from b's [[meta]] fact, and the free flag passes as long as the token is held. Free consumes it, so whoever frees an object must own it, and an object no one else owns cannot be freed behind the owner's back. For a heap object it is exclusive, or split into fractions for readers; for global data, which is never freed, it is persistent.

- The [[runtime]] frees nothing: at a [[poll|safepoint]] the collector changes no region (Runtime.v's [collector_live]), so a program keeps its tokens across a safepoint. Only code the program brings in, a signal handler it installs or a thread it starts, could free under it, and that code is the program's to verify. Hi.v still states its stdio objects' liveness as `stdio_stable`.
- A flag-only [[renew]] asks for nothing but this token.

See [logic.md, Where the proposal is right](../logic.md#where-the-proposal-is-right).

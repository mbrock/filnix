# weakest precondition / WP

**Iris** · Dijkstra 1975; iris/program_logic/weakestpre.v

`WP e {{ v, Φ v }}` says that running e is safe and that, if it ends in a value v, Φ v holds. Iris defines it once for every language by guarded recursion: unless e is a value, given the [[state-interpretation|state interpretation]] of any state, e can step (when stuckness is NotStuck), and after every step it can take, one [[later-modality|later]] on, the new state's interpretation and the WP of what e became hold. Hoare [[hoare-triple|triples]] and specifications are wands into it.

- In nanofil's Iris language a configuration that [fails] cannot step, so a NotStuck WP of the entry call says no reachable configuration fails, and Iris's [[adequacy]] makes that [never_panics]. The spike's `wpc e` is the WP with postcondition True.

See [How Iris works, Weakest preconditions](../iris.md#weakest-preconditions).

# FUGC / garbage collector / collector / soft handshake / store barrier / free singleton

**Fil-C** · [FUGC](https://fil-c.org/fugc), [safepoints, soft handshakes](https://fil-c.org/safepoints#softhandshake), [fugc.c](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/fugc.c)

FUGC, Fil's Unbelievable Garbage Collector, is what reclaims memory in Fil-C. It marks and sweeps on its own threads, in parallel, while the program runs, and never moves an object. It never stops the world: it asks each thread for work, such as scanning its stack, by a soft handshake, which the thread answers at its next [[poll|pollcheck]]. While it marks, a store barrier marks the target of every pointer stored to the heap. It finds pointers exactly: on stacks through the [[root|roots]] the compiler keeps, and in objects only in their [[aux]] allocation.

- `free` does not wait for it. Free empties the object's bounds and raises its free flag at once, so every later access through any pointer to it [[trap|panics]]. FUGC then repoints every [[lower]] of the freed object at one shared free singleton and reclaims the memory. Use after free and double free are caught even after the memory is reused, and an object never freed is still reclaimed.
- The model has one thread and no collector. What FUGC and other threads may do at a safepoint is stated as [[runtime]] axioms: no object moves ([non_moving]), nothing the program can name is reclaimed ([rooting]), and a free changes no byte ([[retention]]).

# retention

**nanofil** · free changes only the header; [[fugc|FUGC]] reclaims the memory once no [[lower]] names it ([FUGC](https://fil-c.org/fugc))

Retention is the [[runtime]] axiom that free changes no byte and no stored capability: a freed object's memory stays as it was while anything can name it. Only its header changes, so every access through a capability to it traps, but bytes read through a check that passed before the free are the same bytes.

- Runtime.v's [retention], proved for the interpreter by [free_res_retention]; natively `free_impl` writes only the header. Native test: axiom-retention.c (another thread frees the object a loop reads and churns the allocator; the loop reads retained bytes or traps, never other values).
- With [non_moving] it makes another thread's free between a check and its access harmless natively: the access reads retained bytes, and the next check traps. The one-threaded model has no such free; its safepoint changes no region ([collector_live]).

It is also why a pointer store stays safe natively when its [[aux]] exit runs a handler the program installed that frees the object: the store lands in retained memory, as Fil-C's own argument at that exit says. The model leaves such handlers out, so every runtime meets [[spares]].

See [runtime-axioms.md, The axioms](../runtime-axioms.md#the-axioms).

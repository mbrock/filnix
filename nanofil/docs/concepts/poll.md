# poll / pollcheck / safepoint / poll edge

**Fil-C** · [safepoints](https://fil-c.org/safepoints#pollchecks), [filc_runtime.c](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.c)

A safepoint is a point where the thread may run signal handlers and answer the collector, so where an object may be freed under the program. A pollcheck is a safepoint on an edge: a jump target `poll(L)`, a poll edge, runs one before going to L. Calls, allocations and some helpers are safepoints too (`ir:evidence_preserving/1`, `ir:polls_every_cycle/1`).

- Upstream puts a pollcheck on every back edge of the control-flow graph, not only on loops. A thread about to block in a system call first *exits*, and the collector does its handshake work for it ([[fugc|FUGC]]).
- Every cycle of a checked function has a poll edge, so a loop cannot keep the collector waiting ([polls_every_cycle]).
- No [[live-fact|live fact]] crosses a safepoint, with three exceptions that the generic theorem covers by [[spares]].
- Rocq: the target [Poll]; the [[runtime]] acts only before an instruction where [at_safepoint] holds or before a poll edge ([safepoint_due]), as its axiom [safepoints] says.

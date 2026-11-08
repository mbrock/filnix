# snapshot

**nanofil** · the generic convention copies a variadic callee's arguments into a read-only object ([calling convention](https://fil-c.org/calling_convention))

Three things share the name. `tests/snapshot.sh` is the byte-identity gate across revisions: a refactoring must leave every output unchanged. A setjmp function keeps snapshots, copies of every temporary (`filc_amd64:setjmp_snapshots//3`, [setjmp.md](../setjmp.md)). And a variadic callee's argument snapshot is the read-only heap object its extra arguments are copied into at entry.

The last is the one the formal model knows: `interp:entry_snapshot/6`, Semantics.v's point [Snapshot] and the hidden name [va_snapshot]. It is an allocation, so the [[runtime]] may refuse it (`out_of_memory`), and freeing it traps at its renew as natively ([rocq.md, A freed snapshot traps at its renew](../rocq.md#a-freed-snapshot-traps-at-its-renew)).

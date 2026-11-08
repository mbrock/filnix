# access

**nanofil** · SIMD accesses are checked as one access too ([compiler](https://fil-c.org/compiler))

A vector's full-width access check: `access(K, Addr, Size, Align)` traps as a K (`read` or `write`) access of Size bytes at Addr with alignment Align would, and moves no data. It comes before the vector's 8-byte chunks, so the vector traps as one access ([vector-access.md](../vector-access.md)).

[[pizlonate|Pizlonated]], it becomes a [[check]] and a [[touch]] of the check's [[proof]] (`pizlonate:checked_access/4`). Vectors are outside the [[core-subset|core subset]]: the Rocq model has no counterpart, and a function that uses one decodes to [IOutside].

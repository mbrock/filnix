# aux / aux allocation / aux word / atomic box

**Fil-C** · [InvisiCaps at rest](https://fil-c.org/invisicaps#restptr), [filc_runtime.h](https://github.com/pizlonator/fil-c/blob/deluge/libpas/src/libpas/filc_runtime.h)

An object's aux allocation, as large as its payload: where Fil-C keeps the [[lower|lowers]] of the pointers stored in the object, slot for slot, while their intvals sit in the object's bytes. The aux word in the object header points at it; it is null for an object no pointer was ever stored into, which the collector then scans as a leaf. A pointer store must *ensure* it exists, which may call the runtime; a pointer load reads it.

- An entry with its low bit set points at an atomic box, a 16-byte object holding a whole [[flight-pointer|flight pointer]] for a pointer accessed atomically; its lower is at box+8 (`ir:pointer_memory_effects/2`, `filc_amd64:pointer_load_effects//4`). A named local's stack aux has neither header nor box.
- Rocq: [m_aux], the [[capability]] stored at each 8-aligned slot, written by [store_aux] and read by [aux_at]; the [[runtime]] axiom [aux_round_trip] says what a safepoint may do to it.

The subtlety: ensuring aux is a safepoint natively, where a signal handler the program installed may run and free the checked object. That is why a pointer store's facts once needed [[spares]] as a real hypothesis. The model has no handler, so every runtime now meets it and the theorems no longer take it; a verified handler must not free an object whose check is in flight.

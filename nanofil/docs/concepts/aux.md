# aux

An object's auxiliary array: where Fil-C keeps the [[lower|lowers]] of the pointers stored in the object, slot for slot, while their addresses sit in the object's bytes. A pointer store must *ensure* it exists, which may call the runtime; a pointer load reads it.

- An entry with its low bit set is boxed, for a pointer accessed atomically, and the real lower is at box+8 (`ir:pointer_memory_effects/2`, `filc_amd64:pointer_load_effects//4`). A named local's stack aux has neither header nor box.
- Rocq: [m_aux], the [[capability]] stored at each 8-aligned slot, written by [store_aux] and read by [aux_at]; the [[runtime]] axiom [aux_round_trip] says what a safepoint may do to it.

The subtlety: ensuring aux is a safepoint natively, which is why a pointer store's facts need [[spares]].

# raw access

**nanofil**

A raw access is a checked-stage memory access that does no checking of its own and names the [[proof]] that covers it: `raw_load`, `raw_store`, `raw_load_pointer`, `raw_store_pointer`, `raw_cas` and `raw_call` (`ir:covered_access/6`).

- Rocq: the ops [RawLoad] and [RawLoadPointer], the instructions [RawStore], [RawStorePointer] and [RawCall]; [raw_access] transcribes `ir:raw_access/5`.
- At run time it makes its access check again without trapping: where that check would fail the run is [[unchecked]] (`interp:raw_res/2`, [raw_res]). [[covered-access|Coverage]] and [[soundness]] show a valid module never gets there.

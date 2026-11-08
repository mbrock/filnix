# fresh base / fresh

A fresh base is an address where a new object may be placed: positive, aligned, no object's [[identity]] (live or freed), overlapping no object's bounds, ending at or below 2^64, and reading as zero with no stored capability, as Fil-C's allocations do.

- [fresh] in Memory.v, for an allocation request [alloc_req]. Semantics.v's [step] answers [Fresh] at an allocation, and [step_rel] takes any fresh base, so the semantics never depends on where objects go.
- Every [[runtime]]'s [alloc] must choose one ([fresh_allocation]); the [[address-space|address space]] ([address_space]) then bounds the end by 2^48.
- interp.pl's allocator, `interp:alloc_base/6`, takes the next aligned address from 2^32 (`interp:stack_base/1`) and only adds. That is one fresh choice; nothing may rely on it.

The subtlety: fresh is stated over objects as [object_region] finds them, not over every region in the list, so [[ready]] and fresh follow from each other without a lemma about the list's shape.

See [rocq.md, Campaign 3: the machine of a runtime](../rocq.md#campaign-3-the-machine-of-a-runtime).

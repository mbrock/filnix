# meta / meta fact

**nanofil** · proposed, not yet in the model

A meta fact, `meta b n k`, says that the object of [[identity]] b was allocated with extent n bytes and kind k (heap, global data, stack). It is the persistent half of owning an object in the planned program logic: once true it stays true, so it can be copied and shared freely, because nothing after an allocation changes what was allocated. With the pointer's offset from b it decides a [[check]]'s bounds by arithmetic alone; whether the object is still there is the [[live]] token's part.

- It is ghost state: after a free the [[region]]'s bounds are empty, but the meta fact still says what the object was. Runtime.v makes it stable: an identity is never reused ([fresh_allocation]), free keeps every identity ([free_keeps_ids]), and nothing else changes a region's bounds ([free_lifetime], [safepoint_lifetime]).
- Buffer.v's [holds_buffer] contains it for the buffer, written as the region's equation: `meta b 32 Heap` and `live b` in one fact.

See [logic.md, The proposal in one paragraph](../logic.md#the-proposal-in-one-paragraph).

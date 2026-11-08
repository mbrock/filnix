# near offset

**nanofil**

A near offset is one within 2^62 of 0. The validator's offsets between pointers ([[guard-chain|guard chains]], [[pointer-distance|pointer distances]]) are exact only modulo 2^64, because address arithmetic wraps; for a near offset the integer is the true signed distance, so the validator counts only near ones where it compares positions.

- `ir:near_offset/1`; Validate.v's [near_offset].
- Readers: the [[need]] analysis (`ir:raise_need/6`, and a [[check_ahead]]'s K and K + Lo in `ir:ahead_insts/8` and the pass's `schedule:widened/5`), [[half_check]] (`ir:half_known/6`), hull coverage (`ir:hull_covered/7`). `ir:hull_renewable/8` writes the same bound inline.

Why it suffices: with every object below 2^48 ([[address-space|address space]]), two addresses that are near offsets apart, or a near offset from a point inside an object, cannot wrap past each other, so "at or past" between them means what it says.

The subtlety: bounding only the need was not enough; the check's own start K + Lo must be near too, or it can wrap onto the need's end ([rocq.md, A need past 2^64](../rocq.md#a-need-past-264)).

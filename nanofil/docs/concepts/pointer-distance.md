# pointer distance

The pointer distance from P1 to P is a constant D such that P's address is P1's plus D modulo 2^64, and P has P1's [[capability]]. The validator finds it when both pointers reach one [[exact-base|exact base]] on their [[guard-chain|guard chains]]: D is the difference of their offsets from it.

- `ir:pointer_distance/4`; `ir:same_pointer/3` is the case D = 0 modulo 2^64. Validate.v transcribes [pointer_distance], including ir.pl's cut: both take the first base of P's chain that P1's chain shares.
- Readers: [[renew]], [[half_check]] (`ir:half_known/6`), [[renew_hull]] (`ir:hull_renewable/8`) and hull coverage (`ir:hull_covered/7`).
- Chain.v's [pointer_distance_sound] makes it true at run time where the names dominate the point; Renew.v's [distance_pointer] shows P then reads as a pointer, which excludes `unchecked(alias)`.

The subtlety: D is a difference modulo 2^64, so a reader that needs a true signed distance asks it to be a [[near-offset|near offset]] too.

See [schedule.md, Checked-IR evidence](../schedule.md#checked-ir-evidence) and [rocq.md, Reading single definitions](../rocq.md#reading-single-definitions).

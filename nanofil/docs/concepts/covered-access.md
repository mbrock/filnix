# covered access / coverage

**nanofil**

A [[raw-access|raw access]] is covered by a check when it lies inside the checked bytes, at an alignment the check's implies, with [[rights]] the check allows. Its own access check, which the raw access makes again without trapping, then passes too.

- `ir:covered_access/6`, from `ir:raw_access/5`, `ir:access_size_align/3` and `ir:rights_allow/2`; Validate.v's [covered_access].
- Coverage.v's coverage lemma: [cap_access_covered] (a passed check passes for every covered part), [covered_access_checked], [access_ok_not_unchecked], and [covered_access_not_unchecked]: a covered raw access gives no [[unchecked]].

The subtlety: addresses wrap modulo 2^64 ([raw_address], `interp:raw_address/3`) while bounds are unbounded integers, so the lemma needs the [[address-space|address space]] ([objects_fit]): an object ending past 2^64 would let a covered access wrap to address 0. The lemma also assumes the check passes in the memory the access runs in; that it still does is the [[evidence-invariant|evidence invariant]]'s job.

"Coverage" also means, in Campaign 4, native coverage of a contract: that real calls stay within it. That is unrelated.

See [rocq.md, The coverage lemma](../rocq.md#the-coverage-lemma).

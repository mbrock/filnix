# renew_hull / hull

The hull of several passed checks of one object is the interval from the least lower end to the greatest upper end of their spans; since an object is one interval, every byte of the hull is in it. `renew_hull(Lo, Hi, Rights, Align)` of `[QL, QH, P]` is a [[renew]] whose bounds two such checks give: QL's from at or below P+Lo, QH's to at or above P+Hi.

- Two uses: `ir:hull_renewable/8` accepts a renew_hull from two [[renew-source|renew sources]]; `ir:hull_covered/7` accepts a raw access between the spans of the [[live-fact|live facts]] of P's object, related by [[pointer-distance|pointer distance]]. Validate.v: [hull_renewable], [hull_covered].
- Proofs: Chain.v's [cap_access_hull] and [hull_access_not_unchecked] for accesses; Renew.v's [hull_address] and [hull_renew_access] for renews.
- A write needs some span with write rights.

The subtlety: the spans are joined modulo 2^64, and two spans of one object are on the same side of the wrap only if the object is smaller than about 2^63. That is why the [[address-space|address space]] ([objects_fit]) bounds objects by 2^48 rather than 2^64.

See [rocq.md, Objects end below 2^48](../rocq.md#objects-end-below-248) and [forward.md](../forward.md).

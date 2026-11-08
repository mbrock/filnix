# offset interval

**nanofil**

An offset interval bounds the values an integer name can hold, derived through its [[single-definition|single definitions]], so that a [[flight]]'s offset from its base is known to lie in `[Lo, Hi]`. At class `w` it bounds the signed word itself; at `l` it bounds some integer congruent to the value modulo 2^64, which is all address arithmetic needs.

- `ir:offset_interval/8` walks a narrow `ext` or load, `copy`, `and` with a mask, `urem`, `shl` and `mul` by a constant, `add`, and `sub` of a constant (`ir:op_interval/9`), memoised under a depth limit of 32. Validate.v: [oi], [offset_interval].
- Interval.v: [iv], one constructor per clause; [offset_interval_iv] (every answer is derived) and [iv_sound] (a derived interval holds where the names it walks hold their definitions). Chain.v's [interval_at] applies it at a run's point.
- Readers: [[guard-chain|guard chains]], hence [[renew_if]] and the [[need]] analysis.

The subtlety: Prolog's evaluation shows through. The memo keeps successes but not failures, and `op_interval/9` commits after its heads; Validate.v copies both rather than the clauses' logical reading.

See [rocq.md, Offset intervals](../rocq.md#offset-intervals).

# exact base

An exact base of a pointer P is a [[single-definition|single-definition]] name B on P's [[guard-chain|guard chain]] whose offset interval is one point, `B-i(K, K)`: P's address is B's plus exactly K, modulo 2^64, with B's [[capability]].

- ir.pl has no predicate for it; `ir:pointer_distance/4`, `ir:same_pointer/3` and `ir:raise_need/6` each select chain elements with `i(K, K)` whose name is in Once. Validate.v names it [exact_base].
- Readers: [[pointer-distance|pointer distance]] (two pointers with a common exact base), and the [[need]] analysis, which raises the need of each exact base of an accessed pointer.

The subtlety: a base reached through a variable offset is on the chain with a wider interval and serves [[renew_if]]'s guard, but not these readers; and K is exact only modulo 2^64, so readers comparing positions also ask K to be a [[near-offset|near offset]].

See [schedule.md, Validator rule](../schedule.md#validator-rule-irpl-independent-of-the-pass).

# renew

**nanofil** · free sets the upper bound to the lower and raises the free flag ([InvisiCaps](https://fil-c.org/invisicaps))

A renew reuses an earlier check's bounds: `renew(Lo, Hi, Rights, Align)` of `[Q1, P]` trusts the dominating check that made Q1 for P's bounds and tests again only what a free changes, that the object is not freed (and, for a write, not read-only). It is the `-O` default (`check_reuse:renew_checks/2`, [m7.md, round 4](../m7.md#spatial-evidence-and-renewal-round-4)).

- Validator: Q1 is a [[renew-source|renew source]], and P is at a [[pointer-distance|pointer distance]] from its pointer, inside its span.
- interp.pl: `interp:renew_res/4`; Q1 of another capability is `unchecked(alias)`, a failing check not on a freed object `unchecked(span)`. Rocq: the op [Renew], [renew_res]; Renew.v's [renew_not_unchecked] and, along runs, [run_reuse_checked].

Why it is sound: an object's bounds change only by free, which the flag test catches.

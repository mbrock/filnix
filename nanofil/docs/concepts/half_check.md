# half_check / half check

**nanofil**

`half_check(Bound, Lo, Hi, Rights, Align)` of `[Q1, P]` is exactly a check of `[Lo, Hi)` at P that natively tests only one bound, `upper` or `lower`; the other end is known from Q1's earlier check of the same object, P being at a known [[pointer-distance|distance]] from Q1's pointer.

- Validator: `ir:half_known/6`, its offsets [[near-offset|near]]; Q1 is a [[renew-source|renew source]]. interp.pl: `interp:half_bound/6` is the native test and `interp:half_res/4` the result; where the native test disagrees with the whole check the run is `unchecked(half)`.
- Rocq: [half_known], [half_bound], [half_res] transcribe them; Renew.v proves [half_bound_agrees] and [half_access], and along runs [run_reuse_checked].

The subtlety: a lower half check reads its address signed and fails on any freed object, where the whole check fails only outside the bounds. The two agree only because objects start at or above 0 ([[address-space|address space]]) and a freed object's bounds are empty ([freed_bounds]); both were added to the runtime's statements for this proof.

See [half.md](../half.md) and [rocq.md, Renew and the half check](../rocq.md#renew-and-the-half-check).

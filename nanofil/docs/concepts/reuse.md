# reuse / reuse form

Reuse is using earlier [[evidence]] instead of a new [[check]]. `--checks=reuse` deletes a check whose access an earlier [[live-fact|live]] [[proof]] already covers, so the access reads that proof; it works across plain edges and for related pointers at a constant offset (`check_reuse:reuse_checks/2`, [m7.md, round 3](../m7.md#related-pointers-round-3)). A reuse form is any op that trusts evidence other than a check just before it: [[renew]], [[renew_hull]], [[half_check]], [[renew_if]], [[limit|check_limit]] and [[check_ahead]].

- Rocq: reuse of a live fact is Validate.v's [reusing_access] and Evidence.v's [live_access_not_unchecked]; Renew.v's [reuse_form] names the renew, hull and half check. Each form has its own run theorem, assembled in [[soundness]].
- The forms read relations between [[single-definition|single definitions]], which is why they rest on [[dominance]].

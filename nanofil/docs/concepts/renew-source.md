# renew source

A renew source is an earlier [[proof]] that a reuse form trusts for bounds: a single-definition proof Q1 of a single-definition pointer P1, made by a `check`, `check_ahead`, `renew_if`, `check_limit` or `half_check`, recorded with its range and alignment.

- `ir:renew_source_op/6` lists the ops and what each proves; `ir:stage_sources/4` builds the table, empty in a function with setjmp, whose second return the CFG does not show. Validate.v: [renew_source].
- Readers: [[renew]], [[renew_hull]] (two sources) and [[half_check]].
- Renew.v's [renew_source_holds]: Q1 is an operand, so its definition dominates the point and [[replay|replays]]; it holds the pointer P1 held when the check passed, and memory has persisted since, so the object is as the check saw it or freed.

The subtlety: a `check_ahead` can be a source, and a doomed one did not pass, so Renew.v asks every single definition to replay, not only [scope_plain]'s. A renew trusts only the source's bounds; it asks its own [[rights]].

See [rocq.md, Renew and the half check](../rocq.md#renew-and-the-half-check).

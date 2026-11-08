# live fact

**nanofil** · FilPizlonator removes checks it finds redundant ([compiler](https://fil-c.org/compiler))

A live fact `live(Q, P, Lo, Hi, Rights, Align)` is the validator's record that the [[proof]] Q came from a check of P over `[Lo, Hi)` that still holds: no safepoint since, and neither Q nor P redefined. A later raw access through Q that the fact covers needs no check of its own.

- ir.pl: each check-like op adds one in `ir:checked_inst_rest/7`; `ir:evidence_after/3` keeps them across an `ir:evidence_preserving/1` instruction and `ir:evidence_kill/3` drops those naming a redefined name; any other instruction ends them all. Validate.v: [fact], [evidence_after], [kill].
- Its meaning is [fact_holds] (Evidence.v): Q holds a pointer word, P evaluates to the same word, and the access check of that pointer passes in the current memory. A check reads only regions, so a step that changes no region keeps it.
- The [[evidence-invariant|evidence invariant]] proves facts hold along runs; its [live_dom] adds that each fact's pointer has a single definition dominating the point, which [[renew_hull|hull]] coverage needs.

The subtlety: a [[check_ahead]] that dooms its frame leaves a fact that does not hold; the evidence invariant therefore excludes [[doomed]] frames.

See [rocq.md, The evidence invariant, instruction by instruction](../rocq.md#the-evidence-invariant-instruction-by-instruction).

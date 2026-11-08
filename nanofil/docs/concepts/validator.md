# validator

The validator decides whether a module is well formed and, in [[stage|checked IR]], whether every access is covered by evidence that still holds. Every producer of checked IR must get its output past it, and Soundness.v proves that a module it accepts never runs to [[unchecked]].

- Prolog: `ir:valid_module/1`, which throws at the first problem; the checked part is `ir:stage_func/6` (the [[evidence-pass|evidence pass]], `ir:limit_reads/2`, `ir:polls_every_cycle/1`).
- Rocq: [valid] in Validate.v, with [valid_func], [valid_data] and [valid_alias]. It returns false where ir.pl throws, so it follows ir.pl's clause groups, not its order of evaluation. [valid_no_unchecked] is the theorem, [[soundness|soundness of checking]].

The subtlety: the theorem is about Validate.v's transcription, not ir.pl. What ties the two is the [[mutant]] gate, comparing verdicts on every mutant of the corpus, not a proof. Three places where ir.pl's answer depends on Prolog's evaluation (the [[offset-interval|offset interval]] memo, a cut in `ir:pointer_distance/4`, `ir:op_interval/9`'s commits) are copied deliberately.

See [rocq.md, The validator and its gate](../rocq.md#the-validator-and-its-gate) and [rocq.md, No run is unchecked](../rocq.md#no-run-is-unchecked).

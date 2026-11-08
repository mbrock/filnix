# soundness of checking / soundness

Soundness of checking is the validator's theorem: every run of every valid checked module avoids [[unchecked]], so the checks the [[validator]] demands, and those it lets a pass remove or reuse, are enough, and a check that fails is the run's whole story. It does not say a check never fails: a module that reads past an array is valid and traps.

- [valid_no_unchecked] in Soundness.v, over every [[runtime]], with the hypotheses that the module is checked by Validate.v's [valid], that the run starts [[ready]], and [[spares]]; [interp_valid_no_unchecked] under the interpreter's runtime, closed. Its proof hands each source of `unchecked` to a run theorem: [run_doomed_checked], [run_access_checked], [run_reuse_checked], [run_guard_checked], and the axiom [free_checked].
- On the Prolog side it is the claim that `ir:valid_module/1`'s rule is sound, which ir.pl argued and the [[mutant]] gate tests.

Not to be confused with trap-freedom of one program, Campaign 7's `never_panics`, which is per program and builds on this. External calls other than `free` are stuck, so the theorem says nothing past them.

See [rocq.md, No run is unchecked](../rocq.md#no-run-is-unchecked) and [formal.md, The claims, kept apart](../formal.md#the-claims-kept-apart).

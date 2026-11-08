# doomed frame / doomed / doom

**nanofil** · builds on [[check_ahead]]

A frame is doomed after a [[check_ahead]] whose early bytes failed: the check yields its pointer anyway and the frame records the failure, because the validator promised that the frame will reach an access that fails on those bytes before anything observable happens.

- interp.pl: `interp:doomed_result/5`. The doomed run ends `trap(early(Why))` at the failing access, or `unchecked(ahead(Why))` if it first reaches a poll edge, a return or an instruction that is not [[ahead-transparent]]. A renew of another object or a wrong limit stays `unchecked(alias)` or `unchecked(limit)`.
- Rocq: the [fr_doomed] field of [frame], [doomed_result], [edge_step], [jump_step]. Doomed.v proves a doomed frame never steps to `unchecked` ([run_doomed_checked]) with the invariant [dinv] / [doomed_ok]: the [[scope]] holds weakly ([scope_weak]: a doomed proof holds its pointer, not a passed check), memory keeps the doom ([doom_mem]), and the validator's [[need]] at the point covers it ([need_at]).

The subtlety: a doomed frame claims nothing for the [[evidence-invariant|evidence invariant]] or the [[single-definition|single-definition invariant]]; both exclude it, and Doomed.v treats it apart. A doomed frame never calls or returns, so every [[parked|waiting caller]] is undoomed.

See [rocq.md, The doomed frame](../rocq.md#the-doomed-frame) and [schedule.md, Interpreter rule](../schedule.md#interpreter-rule-interppl).

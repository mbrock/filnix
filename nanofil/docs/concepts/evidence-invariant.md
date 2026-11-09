# evidence invariant

**nanofil**

The evidence invariant says that along every run, at the running frame's point, the [[live-fact|live facts]] the [[evidence-pass|evidence pass]] computed for that point hold: each fact's check passes in the current memory, and its pointer has a [[single-definition|single definition]] dominating the point. It is how the pass's static bookkeeping becomes a fact about runs.

- One step at a time (Evidence.v): [fact_holds] is a fact's meaning; [checked_inst_holds] keeps the facts across every case of `ir:checked_inst_rest/7`, [entry_holds] across an unpolled edge into the meet of [[exit-facts|exit facts]].
- The pass read back (Walk.v): [pass_fold], [walks], and [relies], the instructions before which it keeps facts.
- Stated (Invariant.v): [at_pos], [point_ok], [frame_ok], [live_dom], and [inv]: the running frame is `point_ok` unless [[doomed]], every waiting caller [[parked]].
- Over runs (Persistence.v): [mstep_inv]; [run_access_not_unchecked], given [[spares]], which every runtime meets ([spares_any]).

The subtlety: a back edge without a poll carries no facts (the pass had not reached its source), so nothing needs justifying there; a doomed frame claims nothing.

See [rocq.md, The evidence invariant over runs](../rocq.md#the-evidence-invariant-over-runs).

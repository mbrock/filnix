(** Hello decides whether to report a stdout close error before closing stderr.
    A zero result skips the diagnostic. A failure also skips it when the
    ignore flag is set and errno is EPIPE. This proof stops at the two
    branch destinations so callers can supply their separate resources. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import HelloBodies.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld FileInv LibioLogic
  HelloCloseErrno LeavesLogic LibioCloseSteps.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section dispatch.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context `{!Defines ge "__errno_location" errno_location_fn}.
#[local] Hint Opaque live bytes errno_any : typeclass_instances.

(** Testing the ignore flag and errno does not change either value.
    The caller gets them back on both paths, together with all memory it
    supplied. The diagnostic path stops before the string and filename
    loads at L0. *)
Lemma wp_close_stdout_dispatch e r ib ireg flag eb (E : iProp Σ) Φ :
  lookup (TAtom "v5") e = Some (WInt r) -> r = 0 ∨ r = 2 ^ 32 - 1 ->
  lookup (TAtom "closeout#ignore_EPIPE") (ge_globals ge) = Some (mkPtr ib (Obj ib)) ->
  0 < ib -> ib + 1 <= r_end ireg -> r_end ireg <= 2 ^ 63 -> 0 <= flag < 256 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  live ib ireg -∗ bytes ib 0 [flag] -∗ errno_any eb -∗ E -∗
  ((∀ e', live ib ireg -∗ bytes ib 0 [flag] -∗ errno_any eb -∗ E -∗
      WP (ERun (mkFrame close_stdout_fn e' [] None (Enter (TAtom "L91") (Some (TAtom "L8")))) : gexpr) {{ Φ }}) ∧
   (∀ e', live ib ireg -∗ bytes ib 0 [flag] -∗ errno_any eb -∗ E -∗
      WP (ERun (mkFrame close_stdout_fn e' [] None (Enter (TAtom "L0") (Some (TAtom "L8")))) : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame close_stdout_fn e [] None
    (Exec (TAtom "start") (skipn 4 (b_insts (co_block "start"))) (b_jump (co_block "start")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hr [-> | ->] Hignore Hib Hibe Hibr Hflag Hglobal He;
    iIntros "Hil Hib Herr HE HK";
    let b := eval vm_compute in (co_block "start") in change (co_block "start") with b;
    cbn [b_insts b_jump skipn].
  - step. branch. step. branch.
    iDestruct "HK" as "[HK _]". iApply ("HK" with "Hil Hib Herr HE").
  - step. branch. step. step.
    iApply (wp_live_fit1 with "Hil"). iIntros ([Hi0 Hi48]) "Hil".
    check "Hil". load_byte_group "Hil Hib".
    branch_cases.
    + step. step. step. step. branch.
      iDestruct "HK" as "[_ HK]". iApply ("HK" with "Hil Hib Herr HE").
    + step.
      iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
      iApply (wp_glibc_errno_location registry (os_wi w0) ge _ _ Hglobal). resume.
      iApply (wp_close_errno_check eb He); [vx|]. iNext.
      iEval (unfold errno_any) in "Herr".
      iEval (unfold errno_own) in "Herr".
      iDestruct "Herr" as (bs cs [Hbs Hcs]) "Hp".
      rewrite pts_app. iDestruct "Hp" as "[Hb Haux]".
      iApply (wp_close_errno_load eb He with "Hb"); [vx|exact Hbs|].
      iNext. iIntros "Hb".
      iAssert (errno_any eb) with "[Hb Haux]" as "Herr".
      { rewrite /errno_any /errno_own. iExists bs, cs. rewrite pts_app. iFrame. auto. }
      step. step. step. step. step. step.
      branch_cases.
      all: first
        [iDestruct "HK" as "[Hnext _]"; iApply ("Hnext" with "Hil Hib Herr HE")
        |iDestruct "HK" as "[_ Hdiag]"; iApply ("Hdiag" with "Hil Hib Herr HE")].
Qed.
End dispatch.

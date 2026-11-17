(** Hello reports a stdout close error before it exits. The captured body
    loads a filename pointer and selects either a named or unnamed report.
    This proof executes the unnamed path with an explicit error callee
    contract and leaves the named path at its actual entry block.

    Hello passes its messages directly to error without calling a translator.
    The caller must still prove that error can format and print those
    messages with the resources it receives. This module does not prove
    that behavior or the complete close_stdout callback. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic HelloClose.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld OsRegistry
  FileInv LibioLogic LibioCloseSteps HelloCloseErrno LeavesLogic SysCode SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Section diagnostic.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__errno_location" errno_location_fn}
  `{!Defines ge "_exit" glibc__exit}.
#[local] Hint Opaque live live_cap pcell int_cell bytes errno_any : typeclass_instances.

(** Hello tests the filename pointer before it reads any filename bytes.
    A nonzero address reaches L31, where the caller must prove the named
    report using the ownership it supplied. A zero address selects the
    unnamed report, which reads errno and calls error with zero status.
    Hello then exits with the configured failure status.

    The caller lends resources R to error and receives resources Q if it
    returns. These resources may include stderr, the remaining stream list
    and cleanup state. The call may change errno; resources E stay with
    the caller throughout the call. No filename bytes are assumed. *)
Lemma wp_close_stdout_diagnostic e nb nreg filename preg xc xreg status eb fmt text namedfmt
    errorfn errorframe (R Q E : iProp Σ) Φ :
  lookup (TAtom "closeout#file_name") (ge_globals ge) = Some (mkPtr nb (Obj nb)) ->
  0 < nb -> nb mod 8 = 0 -> nb + 8 <= r_end nreg -> r_end nreg <= 2 ^ 63 ->
  0 <= ptr_addr filename < 2 ^ 64 ->
  lookup (TAtom "closeout#str.52") (ge_globals ge) = Some namedfmt ->
  lookup (TAtom "closeout#str.53") (ge_globals ge) = Some text ->
  lookup (TAtom "closeout#str.55") (ge_globals ge) = Some fmt ->
  lookup (TAtom "exit_failure") (ge_globals ge) = Some (mkPtr xc (Obj xc)) ->
  0 < xc -> xc + 4 <= r_end xreg -> r_end xreg <= 2 ^ 63 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  find_fn ge (TAtom "error") = Some (Defined errorfn) ->
  (forall n, call_frame errorfn [WInt 0; WInt n; WPtr fmt; WPtr text] = Some (errorframe n)) ->
  (forall n, 0 <= n < 2 ^ 32 -> ⊢ errno_any eb -∗ R -∗
    WP (ERun (errorframe n) : gexpr)
      {{ v, ⌜v = RetVoid⌝ ∗ errno_any eb ∗ Q }}) ->
  live nb nreg -∗ pcell nb 0 filename -∗ live_cap (ptr_cap filename) preg -∗
  live xc xreg -∗ int_cell xc 0 status -∗ errno_any eb -∗ R -∗ E -∗
  (∀ e', ⌜ptr_addr filename <> 0⌝ -∗
    ⌜lookup (TAtom "v28") e' = Some (WPtr filename) ∧
      lookup (TAtom "v22") e' = Some (WPtr namedfmt) ∧
      lookup (TAtom "v23") e' = Some (WPtr text)⌝ -∗
    live nb nreg -∗ pcell nb 0 filename -∗ live_cap (ptr_cap filename) preg -∗
    live xc xreg -∗ int_cell xc 0 status -∗ errno_any eb -∗ R -∗ E -∗
    WP (ERun (mkFrame close_stdout_fn e' [] None
      (Enter (TAtom "L31") (Some (TAtom "L0")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame close_stdout_fn e [] None
    (Enter (TAtom "L0") (Some (TAtom "L8")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hname Hnb Hnba Hnbe Hnbr Hpr Hnamed Htext Hfmt Hexit Hxc Hxce Hxcr Hglobal He Herror Hframe Hcall.
  iIntros "Hnl Hnp Hpl Hxl Hstatus Herr HR HE Hnamed".
  iApply (wp_live_fit1 with "Hnl"). iIntros ([Hn0 Hn48]) "Hnl".
  step. step. step. step. check "Hnl". load "Hnl" "Hnp" "Hpl".
  destruct (Z.eq_dec (ptr_addr filename) 0) as [Hz | Hnz].
  - step. step. branch_as true. step.
    iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
    iApply (wp_glibc_errno_location registry (os_wi w0) ge _ _ Hglobal). resume.
    iApply (wp_close_errno_check eb He); [vx |]. iNext.
    iEval (unfold errno_any) in "Herr".
    iEval (unfold errno_own) in "Herr".
    iDestruct "Herr" as (bs cs [Hbs Hcs]) "Hp".
    rewrite pts_app. iDestruct "Hp" as "[Hb Haux]".
    iApply (wp_close_errno_load eb He with "Hb"); [vx | exact Hbs |].
    iNext. iIntros "Hb".
    iAssert (errno_any eb) with "[Hb Haux]" as "Herr".
    { rewrite /errno_any /errno_own. iExists bs, cs. rewrite pts_app. iFrame. auto. }
    step.
    iApply wp_call_bind; [vx | exact Herror | apply Hframe |]. iNext.
    iApply (wp_wand with "[Herr HR]").
    { iApply (Hcall with "Herr HR"). apply Z.mod_pos_bound. lia. }
    iIntros (v) "(-> & Herr & HQ)". resume.
    step. step. step.
    iApply (wp_live_fit1 with "Hxl"). iIntros ([Hx0 Hx48]) "Hxl".
    check "Hxl". iEval (unfold int_cell) in "Hstatus".
    iDestruct "Hstatus" as "[%Hstatus Hb]". load_s32 "Hxl" "Hb".
    iApply wp_call_bind; [vx | apply defines | reflexivity |]. iNext.
    iApply (SysWrappers.wp_glibc__exit Hreg Hext). reflexivity.
  - step. step. branch_as false.
    iApply ("Hnamed" with "[%] [%] Hnl Hnp Hpl Hxl Hstatus Herr HR HE"); try assumption.
    repeat split; reflexivity.
Qed.
End diagnostic.

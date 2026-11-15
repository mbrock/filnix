(** A returning error report restores the cancellation setting it saved
    before printing. This proof reads that saved cell and calls the actual
    setcancelstate function with a null output pointer. A nested report
    that saved one leaves cancellation disabled.

    Restoring zero permits the caller to rebuild its cleanup invariant,
    provided it also kept the original cleanup pointers. The flag alone
    does not supply those pointers or the thread's lifetime. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld OsRegistry FileInv LibioLogic LibioCloseSteps SysWrappers
  PrintfStateCode CancelState ErrorCode ErrorEntry Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic OsWorld SysWrappers.
Open Scope Z_scope.

Section restore.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The old flag selects the actual enable or already-disabled path.
    Neither path writes an old-state output cell because that pointer is null. *)
Lemma wp_error_restore_cancel old fr tb treg Φ :
  call_frame glibc___pthread_setcancelstate [WInt old;WPtr null] = Some fr ->
  old = 0 \/ old = 1 -> ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  live tb treg -∗ int_cell tb 792 1 -∗
  ▷ (live tb treg -∗ int_cell tb 792 old -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof.
  intros Hfr [-> | ->] Hself Htb Hta Hte Htr; iIntros "Ht Hflag HK".
  - iApply (wp_cancel_restore Hreg Hext with "Ht Hflag HK"); assumption.
  - iApply (wp_cancel_keep_disabled Hreg Hext with "Ht Hflag HK"); assumption.
Qed.

(** The join reads the saved flag rather than consulting mutable errno.
    All resources in E, including argument snapshots, remain untouched. *)
Lemma wp_error_restore e from status errnum fmt ap mode cb old tb treg (E : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb -> old = 0 \/ old = 1 ->
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  find_fn ge (TAtom "__GI___pthread_setcancelstate") = Some (Defined glibc___pthread_setcancelstate) ->
  live tb treg -∗ int_cell tb 792 1 -∗
  live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗ E -∗
  (live tb treg -∗ int_cell tb 792 old -∗
    live cb (mkRegion cb (cb + 16) Heap Live) -∗ int_cell cb 0 old -∗ E -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.join") (Some from))) : gexpr) {{ Φ }}.
Proof.
  intros Hinputs Hold Hself Htb Hta Hte Htr Hcancel.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Ht Hflag Hl Hsaved HE HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hcb Hcb48]) "Hl".
  cbn in Hcb48.
  assert (Hce : cb + 4 <= r_end (mkRegion cb (cb + 16) Heap Live)) by (cbn; lia).
  step. check "Hl". iDestruct "Hsaved" as "[%Holdrange Hbytes]".
  load_s32 "Hl" "Hbytes".
  destruct Hold as [-> | ->].
  all: iApply wp_call_bind; [vx | exact Hcancel | reflexivity |]; iNext.
  - iApply (wp_error_restore_cancel _ _ tb treg with "Ht Hflag");
      try reflexivity; try assumption; try tauto.
    iNext. iIntros "Ht Hflag". resume. iApply wp_ret_void. iNext.
    iApply ("HK" with "Ht Hflag Hl [Hbytes] HE"). iSplit; [done | iExact "Hbytes"].
  - iApply (wp_error_restore_cancel _ _ tb treg with "Ht Hflag");
      try reflexivity; try assumption; try tauto.
    iNext. iIntros "Ht Hflag". resume. iApply wp_ret_void. iNext.
    iApply ("HK" with "Ht Hflag Hl [Hbytes] HE"). iSplit; [done | iExact "Hbytes"].
Qed.

(** An enabled cleanup invariant needs both cleanup pointers as well as
    the restored zero flag. This rule cannot turn a disabled flag into zero. *)
Lemma error_restored_cleanup tb treg jb :
  ow_self w0 = mkPtr tb (Obj tb) ->
  0 < tb -> tb mod 8 = 0 -> tb + 796 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  live tb treg -∗ int_cell tb 792 0 -∗
  pcell tb off_cleanup null -∗ pcell tb off_cleanup_jmp jb -∗ tcb_cleanup_inv (ow_self w0).
Proof.
  intros Hself Htb Hta Hte Htr. iIntros "Ht Hflag Hcleanup Hjmp".
  unfold tcb_cleanup_inv. iExists tb, treg, jb. iSplit.
  - iPureIntro. unfold off_cancelhandling. repeat split; auto; lia.
  - iFrame.
Qed.
End restore.

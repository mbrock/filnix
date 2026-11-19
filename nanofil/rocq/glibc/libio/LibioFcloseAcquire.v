(** Fclose acquires the stream lock before closing the descriptor.
    This proof covers the single-threaded path from a free lock when
    the caller has not disabled locking. It stops at the descriptor-close
    branch and returns the stream fields with the held lock. *)

From Glibc Require Import Unit_libio_iofclose_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry FileInv LibioLogic
  SysWrappers LibioCloseSteps.
Import ListNotations ProgramAbbreviations SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Local Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** The thread acquires the lock without changing the stream fields or
    cleanup state. The continuation begins with the stream pointer in
    the two temporaries used by the descriptor-close branch. *)
Lemma wp_fclose_start fr fb freg fl lb lbreg sb sreg Φ :
  let fp := mkPtr fb (Obj fb) in
  call_frame Unit_libio_iofclose_os.fn__IO_new_fclose [WPtr fp] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> has fl io_user_lock = false ->
  single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  (∀ e from, ⌜lookup (TAtom "v0") e = Some (WPtr fp) /\ lookup (TAtom "chk0") e = Some (WPtr fp)⌝ -∗
     tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags fl -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗
     WP (ERun (mkFrame Unit_libio_iofclose_os.fn__IO_new_fclose e [] None (Enter (TAtom "L13") (Some from))) : sexpr) {{ Φ }}) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros fp Hfr. injection Hfr as <-. intros Hfb Hfal Hfend Hfreg Hfl Hul. subst fp.
  iIntros "#Hs Htcb Hl Hfl Hlp Hlk HK".
  unfold file_size in Hfend.
  pose proof Hul as Hul'. unfold has, io_user_lock in Hul'. apply negb_false_iff, Z.eqb_eq in Hul'.
  assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul'; lia).
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Htcb" as (tb treg jb Ht) "Htcb". pose proof Ht as (Hself & Htb & _).
  iAssert (tcb_cleanup_inv (ow_self w0)) with "[Htcb]" as "Htcb".
  { iExists tb, treg, jb. iSplit; [iPureIntro; exact Ht | iExact "Htcb"]. }
  assert (Hsz : ptr_addr (ow_self w0) <> 0) by (rewrite Hself; cbn; lia).
  iDestruct "Hlk" as "(%Hk & Hbl' & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl'"). iIntros ([Hl0 Hl48]) "Hbl'".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  (* start, L18 to L23: the lock is free and the process single-threaded. *)
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. iApply (OsThread.wp_zthread_self_cookie); try self_side; [exact Hsz|]. iNext.
  step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl'". step. check "Hbl'". load_null "Hbl'" "Hbo". step. step. step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl'". check "Hbl'". store_int "Hbl'" "Hb0". load "Hl" "Hlp" "Hbl'". step.
  check "Hbl'". store "Hbl'" "Hbo". step.
  iAssert (lock_state lb lbreg 1 0 (ow_self w0)) with "[Hbl' Hb0 Hb4 Hbo]" as "Hlk".
  { iSplit; [iPureIntro; lia|]. iFrame "Hbl'". iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"]|].
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"]|]. iExact "Hbo". }
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  cbn [edge_label]. iApply ("HK" with "[%] Htcb Hl Hfl Hlp Hlk"). split; lk_prove.
Qed.
End rules.

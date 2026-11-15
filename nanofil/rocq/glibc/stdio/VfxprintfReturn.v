(** After narrow formatting, __vfxprintf releases the lock it took and
    returns the formatter's integer result. This rule covers a free lock
    acquired by a single-threaded caller. Recursive and contended locks
    need different return paths. No cancellation flag is read or restored
    on this path, so the caller can keep that flag in its frame. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps FxprintfNormalCode Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section returning.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Lemma wp_vfxprintf_return e k fb freg fl lb lbreg sb sreg (E : iProp Σ) Φ :
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "iw_1.v60") e = Some (WInt k) -> 0 <= k < 2 ^ 32 ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 0 0 null -∗ E -∗ Φ (Ret (WInt k))) -∗
  WP (ERun (mkFrame glibc_vfxprintf e [] None
    (Enter (TAtom "iw_1.join") (Some (TAtom "iw_1.L8")))) : gexpr) {{ Φ }}.
Proof.
  intros Hpr Hchk Hr Hkr Hfb Hal Hend Hreg Huser.
  iIntros "#Hs Hl Hfl Hlp Hlk HE HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)".
  destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hl0 Hl48]) "Hbl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  step. check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl".
  load_s32 "Hbl" "Hb4". step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo".
  check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". step. step.
  iApply wp_ret; [reflexivity | vx |]. iNext. repeat rewrite (Z.mod_small k (2 ^ 32) Hkr).
  iApply ("HK" with "Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo] HE");
    [iSplit; [done | iExact "Hfl"] |].
  iSplit; [iPureIntro; lia |]. iFrame "Hbl".
  iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"] |].
  iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"] |]. iExact "Hbo".
Qed.
End returning.

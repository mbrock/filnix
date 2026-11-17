(** Fflush releases the lock after its sync call, even when sync failed.
    This rule executes the single-threaded release with recursion count zero.
    It does not read cancellation state, so disabled cancellation can remain
    in the caller's frame. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps FflushCode Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld.
Open Scope Z_scope.

Section unlock.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The entry has already mapped sync's result to zero or EOF. Unlocking
    preserves that result rather than turning a failed sync into success. *)
Lemma wp_fflush_unlock e from k fb freg fl lb lbreg sb sreg (E : iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  (from = TAtom "L109" /\ k = 0) \/ (from = TAtom "iw_1.join" /\ k = 4294967295) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 32768 = 0 ->
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ E -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 136 (mkPtr lb (Obj lb)) -∗
    lock_state lb lbreg 0 0 null -∗ E -∗ Φ (Ret (WInt k))) -∗
  WP (ERun (mkFrame glibc__IO_fflush e [] None (Enter (TAtom "L110") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv0 Hc0 Hfrom Hfb Hal Hend Hreg Huser.
  assert (Hkr : 0 <= k < 2 ^ 32) by (destruct Hfrom as [[_ ->] | [_ ->]]; lia).
  iIntros "#Hs Hl Hfl Hlp Hlk HE HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlk" as "(%Hk & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)".
  destruct Hk as (Hkal & Hkend & Hkreg).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hl0 Hl48]) "Hbl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct "Hfl" as "[%Hflr Hfl]".
  iApply (wp_enter _ _ _ _ _ _ _ _ _ (put (TAtom "v120") (WInt k) e));
    [reflexivity | destruct Hfrom as [[-> ->] | [-> ->]]; reflexivity |]. iNext.
  cbn [b_insts b_jump].
  check "Hl"; load_s32 "Hl" "Hfl"; step; step; branch_as false;
  step; load_s32 "Hl" "Hfl"; step; step; branch_as false;
  step; step; check_persistent "Hsl"; load_byte_persistent "Hsl Hsb"; step; branch;
  step; step; check "Hl"; load "Hl" "Hlp" "Hbl"; step; check "Hbl";
  load_s32 "Hbl" "Hb4"; step; step; step; branch;
  step; step; check "Hl"; load "Hl" "Hlp" "Hbl"; step; check "Hbl"; store "Hbl" "Hbo";
  check "Hl"; load "Hl" "Hlp" "Hbl"; check "Hbl"; store_int "Hbl" "Hb0"; step; step;
  iApply wp_ret; [reflexivity | vx |]; iNext;
  rewrite (Z.mod_small k (2 ^ 32) Hkr);
  iApply ("HK" with "Hl [Hfl] Hlp [Hbl Hb0 Hb4 Hbo] HE");
  [iSplit; [done | iExact "Hfl"] |].
  all: iSplit; [iPureIntro; lia |]; iFrame "Hbl";
    iSplitL "Hb0"; [iSplit; [done | iExact "Hb0"] |];
    iSplitL "Hb4"; [iSplit; [done | iExact "Hb4"] |]; iExact "Hbo".
Qed.
End unlock.

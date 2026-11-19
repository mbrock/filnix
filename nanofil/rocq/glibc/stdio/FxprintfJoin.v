(** After the formatter returns, glibc's __fxprintf_nocancel puts back the
    saved `c: _flags2` bitfield and releases the stream lock that it took
    on entry. This module proves that second half of the wrapper, from the
    join block after the formatter call to the return. The proof holds
    for any formatter that gives the stream back with the same flags and
    lock count, whatever it did to the buffer. *)
From Glibc Require Import Unit_stdioZ2dcommon_fxprintf_os.
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  FxprintfTidy FxprintfStream.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Import SysWrappers LibioCloseSteps Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance fx_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** After the formatter returns, the caller must get its stream back as it
    was before the call. This rule shows that it does: the wrapper puts
    back the original flags word and the caller's lock state, and returns
    the formatter's result as a C int. The rule needs from the frame only
    the result, the stream pointer, the checked pointer to the flags word
    and the saved bitfield. *)
Lemma wp_fx_join e vb fd sb sreg fb a19 f flags2 held r md Φ :
  let fp := mkPtr fb (Obj fb) in
  lookup (TAtom "iw_1.v60") e = Some (WInt r) -> lookup (TAtom "pr.1") e = Some (WPtr fp) ->
  lookup (TAtom "chk2") e = Some (WPtr fp) -> lookup (TAtom "chk19") e = Some (WPtr (mkPtr a19 (Obj fb))) ->
  a19 = fb + 116 -> lookup (TAtom "v107") e = Some (WInt f) -> f = fx_field flags2 ->
  0 <= flags2 < 2 ^ 32 -> Z.land flags2 io_need_lock = 0 ->
  (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  single_ro ge sb sreg -∗ fx_stream vb (ow_self w0) fp fd md (Z.lor flags2 2) (Some (fx_cnt held)) -∗
  ▷ (fx_stream vb (ow_self w0) fp fd md flags2 held -∗ Φ (Ret (WInt (r mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel e [] None
    (Enter (TAtom "iw_1.join") (Some (TAtom "iw_1.L8")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros fp Hr Hpr Hc2 Hc19 Ha19 Hv107 Hf Hf2r Hnl Hcnt.
  iIntros "#Hs Hst HK".
  iDestruct (fx_stream_fx with "Hst") as (fb' freg' fl' lp' Hp') "(Hl & Hfl & Hf2 & Hmd & Hlp & Hk & Hclose)".
  destruct Hp' as (Hfp' & Hal' & Hfb' & Hend' & Hfreg' & Hflr' & Hul' & _ & _ & _).
  unfold fp in Hfp'. injection Hfp' as <-. unfold file_size in Hend'. subst fp a19.
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend1).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48']) "Hl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  assert (Hor : 0 <= Z.lor flags2 2 < 2 ^ 32) by (apply lor_lt32; lia).
  iDestruct "Hf2" as "[_ Hf2]". iDestruct "Hfl" as "[_ Hfl]".
  step. step. check "Hl". load_s32 "Hl" "Hf2". step_named. step_named. step_named. check "Hl".
  assert (Hy : x1 = flags2) by exact (fx_restore_ops flags2 f x x0 x1 Hf2r Hf E E0 E1).
  clear E E0 E1. rewrite Hy. store_int "Hl" "Hf2". clear Hy. iEval (rewrite (Z.mod_small flags2); [|lia]) in "Hf2".
  check "Hl". load_s32 "Hl" "Hfl". step. step.
  unfold io_user_lock in Hul'. branch_as false.
  step. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl".
  iDestruct "Hk" as (lb lreg ->) "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  load "Hl" "Hlp" "Hbl". step. check "Hbl". load_s32 "Hbl" "Hb4". step. step. step.
  destruct held as [c|]; cbn [fx_cnt] in *.
  1: destruct (Hcnt c eq_refl) as [Hc0 Hc1].
  - (* The lock was held c times before the call: decrement the count. *)
    branch_as true. step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_s32 "Hbl" "Hb4".
    step. branch_as true.
    step. step. load "Hl" "Hlp" "Hbl". step. check "Hbl". load_s32 "Hbl" "Hb4". step. check "Hbl".
    store_int "Hbl" "Hb4".
    assert (Hc' : (((c + 1) mod 2 ^ 32 - 1 mod 2 ^ 32) mod 2 ^ 32) mod 2 ^ 32 = c).
    { rewrite (Z.mod_small (c + 1)); [|lia]. change (1 mod 2 ^ 32) with 1.
      rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; lia. }
    iEval (rewrite Hc') in "Hb4". step. step.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    rewrite Z.mod_mod; [|lia]. iApply "HK".
    iApply ("Hclose" $! flags2 (Some c) with "[%] Hl [Hfl] [Hf2] Hmd Hlp [Hbl Hb0 Hb4 Hbo]").
    { exact Hnl. }
    { iSplit; [done | iExact "Hfl"]. }
    { iSplit; [iPureIntro; lia | iExact "Hf2"]. }
    iExists lb, lreg. iSplit; [done|]. iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
  - (* The lock was free before the call: release it. *)
    branch. step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo".
    check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". step. step.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    rewrite Z.mod_mod; [|lia]. iApply "HK".
    iApply ("Hclose" $! flags2 None with "[%] Hl [Hfl] [Hf2] Hmd Hlp [Hbl Hb0 Hb4 Hbo]").
    { exact Hnl. }
    { iSplit; [done | iExact "Hfl"]. }
    { iSplit; [iPureIntro; lia | iExact "Hf2"]. }
    iExists lb, lreg. iSplit; [done|]. iFrame. iPureIntro. unfold int_bytes. split_and!; lia.
Qed.


End rules.

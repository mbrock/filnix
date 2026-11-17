(** __fxprintf_nocancel takes the stream lock before it changes the
    stream's flags2 word. This module proves the lock step for a
    single-threaded process, from the test of the lock owner to the
    formatter block, and hands the rest of the call to FxprintfTail.v.
    A free lock gets this thread as its owner with count 0. A lock that
    this thread already holds gets one more acquisition. The module does
    not cover a lock that another thread holds, which needs the
    compare-and-swap and the wait path. *)
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  PrintfStreamInv FxprintfCode FxprintfTidy FxprintfStream FxprintfTail.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsThread OsWorld SysWrappers PrintfStreamInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Module FxVL := VariadicLogicOn R LG0.
Import PrintfStreamInv SysWrappers LibioCloseSteps FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic FxVL.

(** This fact records where the argument copy lies. The proof keeps it
    as one opaque fact so that arithmetic in the lock code does not carry it. *)
Definition fx_snap_ok (sb : Z) (xs : list word) : Prop :=
  0 < sb /\ sb mod 16 = 0 /\ sb + req_extent (fx_req xs) <= 2 ^ 48.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance fx_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The lock block starts after the wrapper has found that the process is
    single-threaded. The environment holds the stream, the format string,
    the cursor object, the null address and this thread's identity. The
    lock count before the call must leave room for one more acquisition. *)
Lemma wp_fx_lock e vb fd sb sreg fb cb sb' fmt ys mode flags2 held dqf regf (R : iProp Σ) (Q : Z -> Z -> iProp Σ) Φ :
  let fp := mkPtr fb (Obj fb) in let xs := WPtr fp :: WPtr fmt :: ys in
  lookup (TAtom "pr.1") e = Some (WPtr fp) -> lookup (TAtom "chk2") e = Some (WPtr fp) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v13") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  lookup (TAtom "v9") e = Some (WInt 0) -> lookup (TAtom "v25") e = Some (WPtr (ow_self w0)) ->
  ptr_addr (ow_self w0) <> 0 -> 0 <= ptr_addr (ow_self w0) < 2 ^ 64 -> fx_snap_ok sb' xs ->
  0 <= ptr_addr fmt < 2 ^ 64 ->
  mode = 0 \/ mode = 2 ^ 32 - 1 -> (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  fx_vfprintf_rule_at vb fd fp fmt xs mode flags2 held R Q -> 0 < cb /\ cb mod 8 = 0 /\ cb + 32 <= 2 ^ 48 ->
  single_ro ge sb sreg -∗ fx_stream vb (ow_self w0) fp fd mode flags2 held -∗ fx_owner (ow_self w0) held -∗
  pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb' + 16) (Ro sb'))) -∗
  pts (snapshot_ps xs sb' (fx_req xs)) -∗ live_capq dqf (ptr_cap fmt) regf -∗ R -∗
  ▷ (∀ x mode', fx_stream vb (ow_self w0) fp fd mode' flags2 held -∗ fx_owner (ow_self w0) held -∗
     live_capq dqf (ptr_cap fmt) regf -∗ Q x mode' -∗ Φ (Ret (WInt (x mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_fxprintf_nocancel e [] None (Enter (TAtom "L32") (Some (TAtom "L21")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros fp xs Hpr Hc2 Hv2 Hv13 Hv9 Hv25 Hself Hselfr Hok Hfmtr Hmode Hcnt Hfmt Hcok.
  iIntros "#Hs Hst Ho Hcur Hsnap Hfc HR HK".
  iDestruct (fx_stream_fx with "Hst") as (fb' freg fl lp Hp) "(Hl & Hfl & Hf2 & Hmd & Hlp & Hk & Hclose)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hfreg & Hflr & Hul & Hnl & Hf2r & Hmdr).
  unfold fp in Hfp. injection Hfp as <-. unfold file_size in Hend. subst fp xs.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iDestruct "Hfl" as "[_ Hfl]".
  iDestruct "Hk" as (lb lreg ->) "Hlk".
  destruct held as [c|]; cbn [fx_cnt fx_owner] in *.
  - destruct (Hcnt c eq_refl) as [Hc0 Hc1]. iDestruct "Ho" as (dqo rego) "Ho".
    iDestruct "Hlk" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
    iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
    step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl".
    iApply (wp_raw_load_pointer_dq with "Hbl Hbo Ho"); [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hselfr |].
    iNext. iIntros "Hbl Hbo Ho".
    step. step. step. step. branch_symbolic.
    assert (Hown : (((if ptr_addr (ow_self w0) mod 2 ^ 64 =? (0 mod 2 ^ 64) mod 2 ^ 64 then 1 else 0)
      mod 2 ^ 32) mod 2 ^ 32 =? 0) = true).
    { change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0. rewrite (Z.mod_small (ptr_addr (ow_self w0))); [|lia].
      destruct (Z.eqb_spec (ptr_addr (ow_self w0)) 0); [lia | reflexivity]. }
    rewrite Hown. cbn [edge_label].
    step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl".
    iApply (wp_raw_load_pointer_dq with "Hbl Hbo Ho"); [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hselfr |].
    iNext. iIntros "Hbl Hbo Ho".
    step. step. step. branch_symbolic. rewrite Z.eqb_refl. cbn [negb edge_label]. change (0 mod 2 ^ 32 =? 0) with true.
    cbn [edge_label].
    step. step. load "Hl" "Hlp" "Hbl". step. check "Hbl". load_s32 "Hbl" "Hb4". step. check "Hbl".
    store_int "Hbl" "Hb4".
    assert (Hc' : (c mod 2 ^ 32 + 1 mod 2 ^ 32) mod 2 ^ 32 = c + 1).
    { change (1 mod 2 ^ 32) with 1. rewrite (Z.mod_small c); [|lia]. apply Z.mod_small. lia. }
    iEval (rewrite Hc' (Z.mod_small (c + 1)); [|lia]) in "Hb4". step. cbn [edge_label].
    iAssert (lock_inv (ow_self w0) (mkPtr lb (Obj lb)) (Some (c + 1))) with "[Hbl Hb0 Hb4 Hbo]" as "Hlk".
    { iExists lb, lreg. iSplit; [done|]. iFrame "Hbl Hbo". iSplitR; [iPureIntro; lia|].
      iSplitL "Hb0"; [iSplit; [iPureIntro; unfold int_bytes; lia | iExact "Hb0"]|].
      iSplit; [iPureIntro; lia | iExact "Hb4"]. }
    iDestruct ("Hclose" $! flags2 (Some (c + 1)) with "[%] Hl [Hfl] Hf2 Hmd Hlp Hlk") as "Hst".
    { exact Hnl. }
    { iSplit; [done | iExact "Hfl"]. }
    iApply (wp_fx_tail _ (TAtom "L53") vb fd sb sreg fb cb sb' fmt ys mode flags2 (Some c) dqf regf R Q
      with "Hs Hst Hcur Hsnap Hfc HR [HK Ho]").
    all: cycle 12.
    { iNext. iIntros (x md) "Hst Hfc HQ". iApply ("HK" with "Hst [Ho] Hfc HQ"). iExists dqo, rego. iExact "Ho". }
    all: first [exact (proj1 Hok) | exact (proj1 (proj2 Hok)) | exact (proj2 (proj2 Hok)) | exact Hfmtr | exact Hmode | exact Hcnt | exact Hfmt | exact Hcok | lk_prove].
  - iDestruct "Hlk" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
    iApply (wp_live_fit1 with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
    step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_null "Hbl" "Hbo".
    step. step. step. step. branch.
    step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0".
    load "Hl" "Hlp" "Hbl". step. check "Hbl". store "Hbl" "Hbo". step. cbn [edge_label].
    iAssert (lock_inv (ow_self w0) (mkPtr lb (Obj lb)) (Some 0)) with "[Hbl Hb0 Hb4 Hbo]" as "Hlk".
    { iExists lb, lreg. iSplit; [done|]. iFrame "Hbl Hbo". iSplitR; [iPureIntro; lia|].
      iSplitL "Hb0"; [iSplit; [iPureIntro; lia | iExact "Hb0"]|].
      iSplit; [iPureIntro; lia | iExact "Hb4"]. }
    iDestruct ("Hclose" $! flags2 (Some 0) with "[%] Hl [Hfl] Hf2 Hmd Hlp Hlk") as "Hst".
    { exact Hnl. }
    { iSplit; [done | iExact "Hfl"]. }
    iApply (wp_fx_tail _ (TAtom "L26") vb fd sb sreg fb cb sb' fmt ys mode flags2 None dqf regf R Q
      with "Hs Hst Hcur Hsnap Hfc HR [HK Ho]").
    all: cycle 12.
    { iNext. iIntros (x md) "Hst Hfc HQ". iApply ("HK" with "Hst Ho Hfc HQ"). }
    all: first [exact (proj1 Hok) | exact (proj1 (proj2 Hok)) | exact (proj2 (proj2 Hok)) | exact Hfmtr | exact Hmode | exact Hcnt | exact Hfmt | exact Hcok | lk_prove].
Qed.

End rules.

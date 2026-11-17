(** glibc's __fxprintf_nocancel brackets its formatter call with a temporary
    change to the stream: it sets bit 2 of the `c: _flags2` bitfield, so
    that the formatter does not act on thread cancellation, and it holds the
    stream lock. This module proves the wrapper's block between taking the
    lock and calling the formatter, and then hands the rest of the run to
    FxprintfJoin.v.

    The orientation test chooses between the narrow formatter and a wide
    path that converts the format string. This rule takes only the narrow
    path, so its caller must show that the stream is unoriented or narrow. *)
From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity VariadicLogic.
From Glibc Require Import OsWorld OsThread OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  PrintfStreamInv FxprintfCode FxprintfTidy FxprintfStream FxprintfJoin.
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

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance fx_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The second block of the wrapper saves and sets the bitfield, allocates
    the wide-conversion locals that it does not use on a narrow stream, stores
    the format pointer, tests the orientation and calls the formatter. A wide
    stream is outside this rule: the caller must show the mode is narrow. *)
Lemma wp_fx_tail e from vb fd sb sreg fb cb sb' fmt ys mode flags2 held dqf regf (R : iProp Σ) (Q : Z -> Z -> iProp Σ) Φ :
  let fp := mkPtr fb (Obj fb) in let xs := WPtr fp :: WPtr fmt :: ys in
  lookup (TAtom "pr.1") e = Some (WPtr fp) -> lookup (TAtom "chk2") e = Some (WPtr fp) ->
  lookup (TAtom "v2") e = Some (WPtr fmt) -> lookup (TAtom "v13") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  0 < sb' -> sb' mod 16 = 0 -> sb' + req_extent (fx_req xs) <= 2 ^ 48 -> 0 <= ptr_addr fmt < 2 ^ 64 ->
  mode = 0 \/ mode = 2 ^ 32 - 1 -> (forall c, held = Some c -> 0 <= c /\ c + 1 < 2 ^ 32) ->
  fx_vfprintf_rule_at vb fd fp fmt xs mode flags2 held R Q ->
  single_ro ge sb sreg -∗ fx_stream vb (ow_self w0) fp fd mode flags2 (Some (fx_cnt held)) -∗
  pts (va_cursor_ps cb (mkRegion cb (cb + 32) Heap Live) (mkPtr (sb' + 16) (Ro sb'))) -∗
  pts (snapshot_ps xs sb' (fx_req xs)) -∗ live_capq dqf (ptr_cap fmt) regf -∗ R -∗
  ▷ (∀ x mode', fx_stream vb (ow_self w0) fp fd mode' flags2 held -∗ live_capq dqf (ptr_cap fmt) regf -∗
     Q x mode' -∗ Φ (Ret (WInt (x mod 2 ^ 32)))) -∗
  WP (ERun (mkFrame glibc_fxprintf_nocancel e [] None (Enter (TAtom "L16") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros fp xs Hpr Hc2 Hv2 Hv13 Hsb Hsmod Hsend Hfmtr Hmode Hcnt Hfmt.
  iIntros "#Hs Hst Hcur Hsnap Hfc HR HK".
  iDestruct (fx_stream_fx with "Hst") as (fb' freg fl lp Hp) "(Hl & Hfl & Hf2 & Hmd & Hlp & Hk & Hclose)".
  destruct Hp as (Hfp & Hal & Hfb & Hend & Hfreg & Hflr & Hul & Hnl & Hf2r & Hmdr).
  unfold fp in Hfp. injection Hfp as <-. unfold file_size in Hend. subst fp xs.
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend1).
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  iDestruct "Hf2" as "[_ Hf2]".
  step. step. check "Hl". load_s32 "Hl" "Hf2". step_named. step_named. load_s32 "Hl" "Hf2". step_named. step_named. step_named.
  load_s32 "Hl" "Hf2". step_named. step_named. step_named. check "Hl".
  assert (Hx0 : x0 = fx_field flags2) by exact (fx_shift_field flags2 x x0 Hf2r E E0).
  assert (Hx2 : x2 = fx_field flags2) by (eapply fx_shift_field; eassumption).
  assert (Hx6 : x6 = Z.lor flags2 2) by (eapply fx_set_ops; eassumption).
  clear E E1 E2 E3 E4 E5 E6 Hx2.
  rewrite Hx6. store_int "Hl" "Hf2".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b3 [Hb3 [Hb3al Hb3end]]) "Hobj".
  change (b3 mod 16 = 0) in Hb3al.
  assert (Hb3al8 : b3 mod 8 = 0) by (Z.div_mod_to_equations; lia). change (b3 + 16 <= 2 ^ 48) in Hb3end.
  iDestruct (obj_zero_block with "Hobj") as "(Hb3l & Hx & Ha)"; [compute; discriminate |].
  iAssert (live b3 (mkRegion b3 (b3 + 16) Heap Live)) with "Hb3l" as "Hb3l".
  iDestruct (zero_cell_prefix b3 0 8 with "Hx Ha") as "(Hb3c & _ & _)".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b63 _) "_".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (b69 _) "_".
  set (b3reg := mkRegion b3 (b3 + 16) Heap Live) in *. assert (Hb3re : r_end b3reg = b3 + 16) by reflexivity.
  check "Hb3l". store "Hb3l" "Hb3c".
  step. check "Hl". iDestruct "Hmd" as "[_ Hmd]". load_s32 "Hl" "Hmd". step. 
  assert (Hsle : sign_extension (2 ^ 32) (2 ^ 31) (mode mod 2 ^ 32) <=?
    sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32) = true) by (destruct Hmode as [-> | ->]; reflexivity).
  rewrite Hsle. branch.
  step. check "Hb3l". iApply (wp_raw_load_pointer_dq with "Hb3l Hb3c Hfc");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hfmtr |].
  iNext. iIntros "Hb3l Hb3c Hfc".
  assert (Hor : 0 <= Z.lor flags2 2 < 2 ^ 32) by (apply lor_lt32; lia).
  iEval (rewrite (Z.mod_small (Z.lor flags2 2)); [|lia]) in "Hf2".
  iDestruct ("Hclose" $! (Z.lor flags2 2) (Some (fx_cnt held)) with "[%] Hl Hfl [Hf2] [Hmd] Hlp Hk") as "Hst".
  { apply fx_need_lock. exact Hnl. }
  { iSplit; [iPureIntro; apply lor_lt32; lia | iExact "Hf2"]. }
  { iSplit; [iPureIntro; lia | iExact "Hmd"]. }
  iAssert (fx_va (mkPtr cb (Obj cb)) (WPtr (mkPtr fb (Obj fb)) :: WPtr fmt :: ys)) with "[Hcur Hsnap]" as "Hva".
  { iExists cb, sb'. iFrame. iPureIntro. split_and!; auto. }
    iApply (Hfmt with "Hst HR Hva"); [vx |]. iNext. iIntros (r md) "Hst HQ". step.
  iApply (wp_fx_join _ vb fd sb sreg fb _ x0 flags2 held r md with "Hs Hst [HK Hfc HQ]");
    [lk_prove | lk_prove | lk_prove | lk_prove | a2 | lk_prove | exact Hx0 | exact Hf2r | exact Hnl | exact Hcnt |].
  iNext. iIntros "Hst". iApply ("HK" with "Hst Hfc HQ").
Qed.

End rules.

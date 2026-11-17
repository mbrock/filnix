(** When message formatting fails with ENOMEM, error examines stderr's
    orientation. A positive signed mode selects the wide fallback message;
    zero and negative modes skip it. This proof follows both paths and
    leaves the wide printing call as a separate contract. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps ErrorCode ErrorEntry Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic OsWorld.
Open Scope Z_scope.

Section fallback.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The mode cell belongs to the real stderr object. The wide callee
    borrows that ownership and may return an error; its integer result
    does not affect the subsequent counter update. *)
Lemma wp_error_fallback e status errnum fmt ap mode cb sb sreg fb freg dq md
    wide widefn wideframe (R E : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb + 8 <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  0 < fb -> fb + 196 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide ->
  find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) ->
  call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe ->
  (0 < md < 2 ^ 31 -> ⊢ liveq dq fb freg -∗ int_cell fb 192 md -∗ R -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      liveq dq fb freg ∗ int_cell fb 192 md ∗ R }}) ->
  live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗
  int_cell fb 192 md -∗ R -∗ E -∗
  (∀ e' predecessor, ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗
    int_cell fb 192 md -∗ R -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e' [] None
      (Enter (TAtom "iw_2.L19") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L67") (Some (TAtom "iw_2.L23")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Hg Hsb Hsa Hse Hsr Hfb Hfe Hfr Hwide Hfn Hframe Hcall.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Hsl Hsp Hfl [%Hmd Hmb] HR HE HK".
  iApply (wp_live_fit1 with "Hsl"). iIntros ([Hs0 Hs48]) "Hsl".
  iApply (wp_live_fit with "Hfl"). iIntros ([Hf0 Hf48]) "Hfl".
  step. step. check "Hsl".
  iApply (wp_raw_load_pointer_dq with "Hsl Hsp Hfl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
  iNext. iIntros "Hsl Hsp Hfl". step.
  check_read_dq "Hfl" by a2. iNext. iIntros "Hfl".
  load_s32 "Hfl" "Hmb". step. step. step.
  destruct (decide (0 < md < 2 ^ 31)) as [Hpos | Hpos].
  - branch_as false. step. step. step. check "Hsl".
    iApply (wp_raw_load_pointer_dq with "Hsl Hsp Hfl");
      [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; lia |].
    iNext. iIntros "Hsl Hsp Hfl".
    iApply wp_call_bind; [vx | exact Hfn | exact Hframe |]. iNext.
    iApply (wp_wand with "[Hfl Hmb HR]").
    { iApply (Hcall Hpos with "Hfl [Hmb] HR"). iSplit; [done | iExact "Hmb"]. }
    iIntros (v) "H". iDestruct "H" as (r ->) "(Hfl & Hmd & HR)". resume. step.
    iApply ("HK" with "[%] Hsl Hsp Hfl Hmd HR HE").
    unfold error_inputs. repeat split; lk_prove.
  - assert (Hcases : md = 0 \/ 2 ^ 31 <= md) by lia.
    destruct Hcases as [Hz | Hhi]; branch_as true;
      iApply ("HK" with "[%] Hsl Hsp Hfl [Hmb] HR HE");
      [unfold error_inputs; repeat split; lk_prove | iSplit; [done | iExact "Hmb"]
      |unfold error_inputs; repeat split; lk_prove | iSplit; [done | iExact "Hmb"]].
Qed.
End fallback.

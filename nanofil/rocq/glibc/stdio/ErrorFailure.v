(** A negative formatter result makes error read the current errno.
    Only ENOMEM causes a mode check and possible wide fallback. This proof
    keeps the original error argument separate from that mutable errno.
    The fallback may change errno again before counting the report. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps ErrorCode ErrorEntry ErrorFallback Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic OsWorld.
Open Scope Z_scope.

Section failure.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A mode cell is required only after the ENOMEM comparison succeeds.
    Its bounds are evidence about the actual stream, not a new lifetime. *)
Definition error_mode_own fb freg en md : iProp Σ :=
  (if decide (en = 12) then
    ⌜0 < fb /\ fb + 196 <= r_end freg /\ r_end freg <= 2 ^ 63⌝ ∗ int_cell fb 192 md
   else emp)%I.

Lemma wp_error_failure e status errnum fmt ap mode cb sb sreg fb freg dq eb ereg en md
    wide widefn wideframe (R E : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb + 8 <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  0 < eb -> eb + 4 <= r_end ereg -> r_end ereg <= 2 ^ 63 ->
  lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide ->
  find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) ->
  call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe ->
  (0 < md < 2 ^ 31 -> ⊢ liveq dq fb freg -∗ int_cell fb 192 md -∗
    (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ R) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ r, ⌜v = Ret (WInt r)⌝ ∗
      liveq dq fb freg ∗ int_cell fb 192 md ∗
      (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ R) }}) ->
  live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗
  live eb ereg -∗ int_cell eb 0 en -∗ error_mode_own fb freg en md -∗ R -∗ E -∗
  (∀ e' predecessor, ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    live sb sreg -∗ pcell sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗
    live eb ereg -∗ (∃ now, int_cell eb 0 now) -∗ error_mode_own fb freg en md -∗ R -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e' [] None
      (Enter (TAtom "iw_2.L19") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.L22") (Some (TAtom "iw_2.start")))) : gexpr) {{ Φ }}.
Proof.
  intros Hinputs Hg Hsb Hsa Hse Hsr Herrno Heb Hee Her Hwide Hfn Hframe Hcall.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Hsl Hsp Hfl Hel [%Hen Hebytes] Hmd HR HE HK".
  iApply (wp_live_fit1 with "Hel"). iIntros ([He0 He48]) "Hel".
  step. step. check "Hel". load_s32 "Hel" "Hebytes". step. step. step.
  destruct (Z.eq_dec en 12) as [Hen12 | Hen12].
  - branch_as false.
    unfold error_mode_own. rewrite decide_True; [|done].
    iDestruct "Hmd" as "(%Hfb & Hmd)". destruct Hfb as (Hfb & Hfe & Hfr).
    iApply (wp_error_fallback _ status errnum fmt ap mode cb sb sreg fb freg dq md wide widefn wideframe
      (live eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ R)%I E
      with "Hsl Hsp Hfl Hmd [Hel Hebytes HR] HE"); try assumption.
    { unfold error_inputs. repeat split; lk_prove. }
    { iFrame "Hel HR". iExists en. iSplit; [done | iExact "Hebytes"]. }
    iIntros (e' predecessor Hinputs') "Hsl Hsp Hfl Hmd (Hel & Hnow & HR) HE".
    iApply ("HK" with "[%] Hsl Hsp Hfl Hel Hnow [Hmd] HR HE"); [exact Hinputs' |].
    iFrame. done.
  - branch_as true. step. branch.
    iApply ("HK" with "[%] Hsl Hsp Hfl Hel [Hebytes] Hmd HR HE").
    { unfold error_inputs. repeat split; lk_prove. }
    iExists en. iSplit; [done | iExact "Hebytes"].
Qed.
End failure.

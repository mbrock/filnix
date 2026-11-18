(** Error passes its original format and variadic cursor to vfxprintf.
    A nonnegative result goes straight to the report counter. A negative
    result reads errno and may select the wide fallback.

    Formatter and fallback calls remain separate contracts. Their returned
    resources supply the fields the selected path actually reads. No errno
    ownership is required on the successful path, and only ENOMEM needs
    the stream's mode cell. *)
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic Identity.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps ErrorCode ErrorEntry ErrorFailure Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic OsWorld.
Open Scope Z_scope.

Section message.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

Definition error_errno_bounds eb ereg : Prop :=
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) /\
  0 < eb /\ eb + 4 <= r_end ereg /\ r_end ereg <= 2 ^ 63.

(** These fields are lent only when the formatter returned a negative
    signed 32-bit result. The errno value is the one left by that call. *)
Definition error_message_pending_q dqe fb freg eb ereg r en md : iProp Σ :=
  (if decide (2 ^ 31 <= r mod 2 ^ 32) then
    ⌜error_errno_bounds eb ereg⌝ ∗ liveq dqe eb ereg ∗ int_cell eb 0 en ∗ error_mode_own fb freg en md
   else emp)%I.

(** The fallback can change errno. The retained mode ownership records
    whether the earlier errno comparison required the mode read. *)
Definition error_message_returned_q dqe fb freg eb ereg r en md : iProp Σ :=
  (if decide (2 ^ 31 <= r mod 2 ^ 32) then
    ⌜error_errno_bounds eb ereg⌝ ∗ liveq dqe eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ error_mode_own fb freg en md
   else emp)%I.

Lemma wp_error_message {dqs dqe : dfrac} e from status errnum fmt ap mode cb sb sreg fb freg dq eb ereg
    formatter formatterframe wide widefn wideframe (V : ptr -> iProp Σ)
    (R : iProp Σ) (S : Z -> Z -> Z -> iProp Σ) (E : iProp Σ) Φ :
  error_inputs e status errnum fmt ap mode cb ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr sb (Obj sb)) ->
  0 < sb -> sb mod 8 = 0 -> sb + 8 <= r_end sreg -> r_end sreg <= 2 ^ 63 ->
  0 <= fb < 2 ^ 64 ->
  find_fn ge (TAtom "__vfxprintf") = Some (Defined formatter) ->
  call_frame formatter [WPtr (mkPtr fb (Obj fb));WPtr fmt;WPtr ap;WInt (mode mod 2 ^ 32)] = Some formatterframe ->
  lookup (TAtom "glibc_error#str.253") (ge_globals ge) = Some wide ->
  find_fn ge (TAtom "__GI_fputws_unlocked") = Some (Defined widefn) ->
  call_frame widefn [WPtr wide;WPtr (mkPtr fb (Obj fb))] = Some wideframe ->
  (⊢ liveq dq fb freg -∗ V ap -∗ R -∗ WP (ERun formatterframe : gexpr)
    {{ v, ∃ r en md, ⌜v = Ret (WInt r)⌝ ∗ liveq dq fb freg ∗ V ap ∗
      error_message_pending_q dqe fb freg eb ereg r en md ∗ S r en md }}) ->
  (forall r en md, 0 < md < 2 ^ 31 -> ⊢ liveq dq fb freg -∗ int_cell fb 192 md -∗
    (liveq dqe eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ S r en md) -∗
    WP (ERun wideframe : gexpr) {{ v, ∃ result, ⌜v = Ret (WInt result)⌝ ∗
      liveq dq fb freg ∗ int_cell fb 192 md ∗
      (liveq dqe eb ereg ∗ (∃ now, int_cell eb 0 now) ∗ S r en md) }}) ->
  liveq dqs sb sreg -∗ pcellq dqs sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗ R -∗ E -∗
  (∀ e' predecessor r en md, ⌜error_inputs e' status errnum fmt ap mode cb⌝ -∗
    liveq dqs sb sreg -∗ pcellq dqs sb 0 (mkPtr fb (Obj fb)) -∗ liveq dq fb freg -∗ V ap -∗
    error_message_returned_q dqe fb freg eb ereg r en md -∗ S r en md -∗ E -∗
    WP (ERun (mkFrame glibc_error_internal e' [] None
      (Enter (TAtom "iw_2.L19") (Some predecessor))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_error_internal e [] None
    (Enter (TAtom "iw_2.start") (Some from))) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hinputs Hg Hsb Hsa Hse Hsr Hfb Hfmtfn Hfmtframe Hwide Hfn Hframe Hformat Hwidecall.
  destruct Hinputs as (Hstatus & Herrnum & Hfmt & Hap & Hmode & Hsave & Hchk).
  iIntros "Hsl Hsp Hfl HV HR HE HK".
  iApply (wp_live_fit with "Hsl"). iIntros ([Hs0 Hs48]) "Hsl".
  step. step. check_read_dq "Hsl" by a2. iNext. iIntros "Hsl".
  iApply (wp_raw_load_pointer_dq with "Hsl Hsp Hfl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hfb |].
  iNext. iIntros "Hsl Hsp Hfl".
  iApply wp_call_bind; [vx | exact Hfmtfn | exact Hfmtframe |]. iNext.
  iApply (wp_wand with "[Hfl HV HR]"); [iApply (Hformat with "Hfl HV HR") |].
  iIntros (v) "H". iDestruct "H" as (r en md ->) "(Hfl & HV & Hfields & HS)". resume. step.
  destruct (Z_le_dec (2 ^ 31) (r mod 2 ^ 32)) as [Hneg | Hneg].
  - branch_as false. unfold error_message_pending_q.
    rewrite decide_True; [|done].
    iDestruct "Hfields" as "(%Hbounds & Hel & Hen & Hmd)".
    destruct Hbounds as (Herrno & Heb & Hee & Her).
    iApply (wp_error_failure _ status errnum fmt ap mode cb sb sreg fb freg dq eb ereg en md
      wide widefn wideframe (S r en md) (V ap ∗ E)%I
      with "Hsl Hsp Hfl Hel Hen Hmd HS [$HV $HE]"); try assumption; try apply Hwidecall.
    { unfold error_inputs. repeat split; lk_prove. }
    iIntros (e' predecessor Hinputs') "Hsl Hsp Hfl Hel Hnow Hmd HS [HV HE]".
    iApply ("HK" $! e' predecessor r en md with "[%] Hsl Hsp Hfl HV [Hel Hnow Hmd] HS HE"); [exact Hinputs' |].
    unfold error_message_returned_q. rewrite decide_True; [|done]. iFrame.
    iPureIntro. repeat split; assumption.
  - assert (Hpositive : 0 <= r mod 2 ^ 32 < 2 ^ 31).
    { pose proof (Z.mod_pos_bound r (2 ^ 32) ltac:(lia)). lia. }
    branch_as true. step. branch. step. branch.
    iApply ("HK" $! _ _ r en md with "[%] Hsl Hsp Hfl HV [] HS HE").
    { unfold error_inputs. repeat split; lk_prove. }
    unfold error_message_returned_q. rewrite decide_False; done.
Qed.
End message.

(** Most callers own errno's lifetime outright, so the old names keep
    that whole share. A caller that holds only a share of the lifetime
    uses the forms ending in _q. *)
Notation error_message_pending := (error_message_pending_q (DfracOwn 1)).
Notation error_message_returned := (error_message_returned_q (DfracOwn 1)).

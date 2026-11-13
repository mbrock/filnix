(** This module proves that the code the backend emits for integer
    division computes what the IR defines. The IR's `div`, `udiv`,
    `rem` and `urem` are total: Ops.v gives them a result for every
    pair of operands, including a zero divisor and the least signed
    integer divided by -1. The processor's divide instructions fault
    on exactly those operands. The theorem says that the emitted
    sequence never faults and always leaves the IR's result.

    The statement is about the lines that EmitOps.v emits, read by
    Amd64Asm.v and executed by Amd64Step.v. It covers both integer
    classes, both signednesses, and both the quotient and the
    remainder. It holds for every initial state of the registers and
    flags and for every value that an undefined flag may take.

    The proof joins two halves. Amd64DivisionCode.v shows that each
    emitted fragment computes one stage of the operand rewriting, and
    Amd64Total.v shows that the divide of the rewritten operands
    yields the IR's result.

    The theorem trusts three things that it does not prove. The typed
    semantics of Amd64Step.v is a transcription of the processor
    manuals. The reading of Amd64Asm.v states what GNU as takes each
    line to mean. The encoder of Encode.v, or GNU as, turns the lines
    into the bytes that the processor runs. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Syntax Values.
From Nanofil Require Ops.
From Backend Require Import Asm Layout EmitOps.
From Backend Require Import Amd64Word Amd64Machine Amd64Step Amd64Asm Amd64Total
  Amd64DivisionCode.
Import ListNotations.
Local Open Scope Z_scope.

(** ## The theorem on typed code

    The first form of the theorem is about the typed sequence
    [division_code]. It relates the registers before the sequence to
    the registers after it, with the IR's operation applied to the
    operand patterns that the sequence reads. *)

(** The relation [division_result_in_rax] is the postcondition of an
    emitted division. The operands are the low parts of `%rax` and
    `%rcx` in the initial state s, read at the size z of the class k.
    The whole of `%rax` in the final state holds the integer that the
    IR operation returns for them, so a 32-bit result is zero-extended.
    Every register other than the three scratch registers is
    unchanged. The relation says nothing about the flags, which the
    sequence leaves in an unspecified state. *)
Definition division_result_in_rax (sg : signedness) (remainder : bool) (k : class)
    (z : size) (s s' : machine) : Prop :=
  Ops.alu (division_op sg remainder) k [WInt (get_reg z RAX s); WInt (get_reg z RCX s)]
  = Some (WInt (regs s' RAX))
  /\ scratch_only s s'.

(** Division must leave registers other than `%rax`, `%rcx` and `%rdx`
    unchanged. If each part preserves those registers, running the
    parts in sequence preserves them too. *)
Lemma division_scratch_trans (s s' s'' : machine) :
  scratch_only s s' -> scratch_only s' s'' -> scratch_only s s''.
Proof.
  intros H H' r Ha Hc Hd. rewrite (H' r Ha Hc Hd). apply H; assumption.
Qed.

(** The two operand rewritings leave the safe dividend and divisor in
    their registers. Their range bounds ensure that later reads keep
    them unchanged. *)
Lemma division_operands_spec (sg : signedness) (z : size) :
  word_size z ->
  establishes (fun _ => True)
    (zero_divisor_code z ++ minus_one_divisor_code sg z)
    (fun s s' =>
       regs s' RAX = safe_dividend sg z (get_reg z RAX s) (get_reg z RCX s)
       /\ regs s' RCX = safe_divisor sg z (get_reg z RCX s)
       /\ scratch_only s s').
Proof.
  intros Hz. destruct sg.
  - eapply establishes_weaken.
    + eapply establishes_app.
      * apply zero_divisor_spec; exact Hz.
      * apply minus_one_divisor_spec; exact Hz.
      * intros; exact I.
    + intros; exact I.
    + intros s s'' _ [s' [[Ha [Hc Hframe]] [Ha' [Hc' Hframe']]]].
      assert (Hread_a : get_reg z RAX s' =
          nonzero_dividend (get_reg z RAX s) (get_reg z RCX s)).
      { unfold get_reg. rewrite Ha. apply wrap_small.
        apply nonzero_dividend_range. apply wrap_range. }
      assert (Hread_c : get_reg z RCX s' = nonzero_divisor (get_reg z RCX s)).
      { unfold get_reg. rewrite Hc. apply wrap_small.
        pose proof (nonzero_divisor_range z (get_reg z RCX s)
          (wrap_range z (regs s RCX))) as Hrange.
        unfold get_reg in Hrange. lia. }
      rewrite Hread_a, Hread_c in Ha'. rewrite Hread_c in Hc'.
      split; [exact Ha'|]. split; [exact Hc'|].
      eapply division_scratch_trans; eassumption.
  - unfold minus_one_divisor_code. rewrite app_nil_r.
    exact (zero_divisor_spec z Hz).
Qed.

(** The last two fragments select the quotient or remainder of safe
    operands. The remainder's range bound makes its final register
    read exact. *)
Lemma division_finish_spec (sg : signedness) (remainder : bool) (z : size) :
  word_size z ->
  establishes (fun s => divisor_safe sg z (get_reg z RCX s))
    (divide_code sg z ++ result_code remainder z)
    (fun s s' =>
       regs s' RAX =
         (if remainder then machine_remainder else machine_quotient)
           sg z (get_reg z RAX s) (get_reg z RCX s)
       /\ scratch_only s s').
Proof.
  intros Hz. destruct remainder.
  - eapply establishes_weaken.
    + eapply establishes_app.
      * apply divide_spec; exact Hz.
      * apply result_spec; exact Hz.
      * intros; exact I.
    + intros s Hsafe; exact Hsafe.
    + intros s s'' Hsafe [s' [[Ha [Hd Hframe]] [Ha' Hframe']]].
      split.
      * rewrite Ha'. unfold get_reg. rewrite Hd. apply wrap_small.
        apply machine_remainder_range; [apply wrap_range | exact Hsafe].
      * eapply division_scratch_trans; [exact Hframe|].
        intros r Hr _ _. apply Hframe'; exact Hr.
  - unfold result_code.
    rewrite app_nil_r. eapply establishes_weaken.
    + apply divide_spec; exact Hz.
    + intros s Hsafe; exact Hsafe.
    + intros s s' _ [Ha [_ Hframe]]. split; assumption.
Qed.

(** Every execution of the typed division sequence completes, and it
    leaves the IR's result in `%rax`. The precondition is trivial: the
    sequence is correct from every state. *)
Theorem division_code_correct (sg : signedness) (remainder : bool) (k : class)
    (z : size) :
  class_size k = Some z ->
  establishes (fun _ => True) (division_code sg remainder z)
    (division_result_in_rax sg remainder k z).
Proof.
  intros Hk.
  assert (Hz : word_size z).
  { destruct k; inversion Hk; subst; unfold word_size; auto. }
  assert (Hreads : forall s s',
      regs s' RAX = safe_dividend sg z (get_reg z RAX s) (get_reg z RCX s) ->
      regs s' RCX = safe_divisor sg z (get_reg z RCX s) ->
      get_reg z RAX s' = safe_dividend sg z (get_reg z RAX s) (get_reg z RCX s)
      /\ get_reg z RCX s' = safe_divisor sg z (get_reg z RCX s)).
  { intros s s' Ha Hc. unfold get_reg in *. rewrite Ha, Hc.
    split; apply wrap_small.
    - apply safe_dividend_range. apply wrap_range.
    - pose proof (safe_divisor_safe sg z (wrap z (regs s RCX))
        (wrap_range z (regs s RCX))) as Hsafe.
      destruct sg; cbn [divisor_safe] in Hsafe; lia. }
  unfold division_code. rewrite app_assoc.
  eapply establishes_weaken.
  - eapply establishes_app.
    + apply division_operands_spec; exact Hz.
    + apply division_finish_spec; exact Hz.
    + intros s s' _ [Ha [Hc _]].
      destruct (Hreads s s' Ha Hc) as [_ Hread_c]. rewrite Hread_c.
      apply safe_divisor_safe. apply wrap_range.
  - intros; exact I.
  - intros s s'' _ [s' [[Ha [Hc Hframe]] [Hresult Hframe']]].
    destruct (Hreads s s' Ha Hc) as [Hread_a Hread_c].
    rewrite Hread_a, Hread_c in Hresult.
    unfold division_result_in_rax. split.
    + rewrite Hresult. destruct remainder.
      * apply total_remainder_agrees; [exact Hk | apply wrap_range | apply wrap_range].
      * apply total_quotient_agrees; [exact Hk | apply wrap_range | apply wrap_range].
    + eapply division_scratch_trans; eassumption.
Qed.

(** ## The theorem on emitted lines

    A user of the compiler runs the assembly that the backend prints,
    not a typed copy of it. This section therefore restates the
    theorem for the printed lines. Those lines are the ones that
    `division` emits after its two loads, and every execution of them
    leaves the IR's result. *)

(** The register part of every emitted integer division is inside the
    model, never faults, and computes the IR's division. *)
Theorem emitted_division_correct (sg : signedness) (remainder : bool) (k : class)
    (z : size) :
  class_size k = Some z ->
  exists code,
    decode_lines (division_lines sg remainder k) = Some code
    /\ establishes (fun _ => True) code (division_result_in_rax sg remainder k z).
Proof.
  intros Hk. exists (division_code sg remainder z). split.
  - apply division_lines_decode; exact Hk.
  - apply division_code_correct; exact Hk.
Qed.

(** This corollary states the same result without the relation
    [establishes]. From any state s, every execution of the emitted
    division ends in a state and not in a fault, and that state holds
    the IR's result. *)
Corollary emitted_division_never_faults (sg : signedness) (remainder : bool)
    (k : class) (z : size) (code : list instr) (s : machine) (o : outcome) :
  class_size k = Some z ->
  decode_lines (division_lines sg remainder k) = Some code ->
  runs code s o ->
  exists s', o = Next s' /\ division_result_in_rax sg remainder k z s s'.
Proof.
  intros Hk Hdecode Hrun.
  destruct (emitted_division_correct sg remainder k z Hk)
    as [code' [Hdecode' Hcorrect]].
  rewrite Hdecode in Hdecode'. inversion Hdecode'; subst code'.
  exact (Hcorrect s o I Hrun).
Qed.

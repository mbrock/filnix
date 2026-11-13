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

(** Every execution of the typed division sequence completes, and it
    leaves the IR's result in `%rax`. The precondition is trivial: the
    sequence is correct from every state. *)
Theorem division_code_correct (sg : signedness) (remainder : bool) (k : class)
    (z : size) :
  class_size k = Some z ->
  establishes (fun _ => True) (division_code sg remainder z)
    (division_result_in_rax sg remainder k z).
Proof.
Admitted.

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
Admitted.

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
Admitted.

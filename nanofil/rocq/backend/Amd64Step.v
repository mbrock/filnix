(** This module gives an execution model to the integer instructions
    that the nanofil backend emits. Asm.v represents an instruction as
    a mnemonic string with operand strings, which is enough to print
    it but says nothing about what it computes. Here each instruction
    is a typed term, and the function [step] says how it changes the
    registers, the flags and the memory of a [machine].

    The model follows the Intel and AMD instruction references for
    each result, each flag and each fault. It covers the instruction
    forms that the theorems about emitted code need, together with
    the other members of the same families: moves and extending moves,
    loads and stores of a frame slot, two-operand arithmetic and
    logic, negation and complement, `setcc`, sign extension of the
    accumulator, and division.

    An instruction form outside the model does not execute as a
    no-operation. The function [step] returns the fault [Unmodeled]
    for it, so a theorem that a sequence runs to completion also shows
    that the model covers every instruction in the sequence.

    A load or a store reads or writes ordinary bytes, as the processor
    does. It checks only that the bytes are mapped, and it makes no
    capability check. The checks that Fil-C requires are separate
    instructions that the compiler emits, and a theorem about them
    belongs to the relation between this machine and the IR.

    Execution here is of a straight-line list of instructions. The
    model has no instruction pointer, labels or branches yet. These
    need a code layout, which is the next addition. *)

From Stdlib Require Import ZArith List Bool Lia.
From Backend Require Import Amd64Word Amd64Memory Amd64Machine.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Instructions

    A typed instruction names its operand size and its registers
    directly, so two instructions that differ only in spelling are the
    same term. The checked interpretation in Amd64Asm.v produces these
    terms from the backend's lines and rejects every line that has no
    typed form. *)

(** A [source] is the operand that an instruction only reads: an
    immediate integer or a register. *)
Inductive source : Type :=
| SImm (n : Z) (* an immediate, reduced to the operand size when it is read *)
| SReg (r : gpr). (* the low part of a register at the operand size *)

(** An [address] is a memory operand of the form `d(%b)`: the content
    of the base register b plus the constant displacement d. The
    backend addresses every frame slot in this form. The forms with an
    index register and a scale are outside the model. *)
Record address : Type := mkAddress {
  address_base : gpr; (* the register that holds the base address *)
  address_displacement : Z (* the constant that is added to the base *)
}.

(** A [binary] operation combines a source with a destination
    register. The operations `cmp` and `test` compute the result of
    `sub` and `and` for the flags alone and do not write the
    destination. *)
Inductive binary : Type := BAdd | BSub | BAnd | BOr | BXor | BCmp | BTest.

(** A [unary] operation rewrites one register: `neg` negates it in
    two's complement and `not` complements every bit. *)
Inductive unary : Type := UNeg | UNot.

(** A [condition] is a test of the flags that `setcc` evaluates. The
    names are the condition suffixes of the mnemonics. *)
Inductive condition : Type :=
| CondE | CondNE (* equal, not equal: the zero flag *)
| CondB | CondBE | CondA | CondAE (* unsigned below, below or equal, above, above or equal *)
| CondL | CondLE | CondG | CondGE (* signed less, less or equal, greater, greater or equal *)
| CondS | CondNS (* the sign flag set, clear *)
| CondO | CondNO (* the overflow flag set, clear *)
| CondP | CondNP. (* the parity flag set, clear *)

(** An [instr] is one integer instruction in typed form. The operand
    order in each constructor is the AT&T order of Asm.v: sources
    first and the destination last. *)
Inductive instr : Type :=
| IMov (z : size) (a : source) (d : gpr)
  (* `mov`: copies the source to the destination at size z *)
| ILoad (z : size) (a : address) (d : gpr)
  (* `mov` from memory: copies the z bytes at the address a to the register d *)
| IStore (z : size) (r : gpr) (a : address)
  (* `mov` to memory: copies the z part of the register r to the bytes at a *)
| IMovzx (za zd : size) (a d : gpr)
  (* `movzb`, `movzw`: zero-extends the za part of a into the zd part of d *)
| IMovsx (za zd : size) (a d : gpr)
  (* `movsb`, `movsw`, `movsl`: sign-extends the za part of a into the zd part of d *)
| IBinary (o : binary) (z : size) (a : source) (d : gpr)
  (* a two-operand arithmetic or logic instruction at size z *)
| IUnary (o : unary) (z : size) (d : gpr)
  (* `neg` or `not` at size z *)
| ISet (c : condition) (d : gpr)
  (* `setcc`: writes 1 or 0 to the low byte of d *)
| IExtend (z : size)
  (* `cltd`, `cqto`: fills the z part of `%rdx` with the sign of the z part of `%rax` *)
| IDivide (sg : bool) (z : size) (c : gpr).
  (* `idiv` when sg holds and `div` otherwise: divides `%rdx`:`%rax` by the z part of c *)

(** ## Outcomes

    An instruction either completes and leaves a new state, or it
    stops the program. This section defines the two ways in which the
    model stops: a fault that the processor raises, and an instruction
    form that the model does not describe. The processor reports an
    access to unmapped memory as a page fault or a general protection
    fault, and the model has one fault for both. *)

(** A [fault] is a reason why an instruction does not complete. *)
Inductive fault : Type :=
| DivideError (* the processor's divide error, raised by `div` and `idiv` *)
| MemoryFault (* a load or a store touched a byte that is not mapped *)
| Unmodeled. (* the instruction form has no semantics in this model *)

(** An [outcome] is the result of executing one instruction or a
    sequence of instructions. *)
Inductive outcome : Type :=
| Next (s : machine) (* execution completed in the state s *)
| Fault (f : fault). (* execution stopped with the fault f *)

(** ## Flags of a result

    The arithmetic instructions set the zero, sign and parity flags
    from their result in one common way, and differ in the carry,
    overflow and auxiliary carry flags. This section defines the flag
    effects that the instruction families share. *)

(** The function [arith_flags] gives the flag effects of an arithmetic
    instruction whose result pattern is v. The caller supplies the
    carry, overflow and auxiliary carry, and the remaining three flags
    follow from the result. *)
Definition arith_flags (z : size) (v : Z) (carry overflow aux : bool)
    (f : flag) : flag_effect :=
  match f with
  | CF => Defined carry
  | OF => Defined overflow
  | AF => Defined aux
  | ZF => Defined (v =? 0)
  | SF => Defined (sign_bit z v)
  | PF => Defined (even_parity v)
  end.

(** The function [logic_flags] gives the flag effects of a bitwise
    logic instruction whose result pattern is v. Such an instruction
    clears the carry and overflow flags and leaves the auxiliary carry
    flag undefined. *)
Definition logic_flags (z : size) (v : Z) (f : flag) : flag_effect :=
  match f with
  | CF | OF => Defined false
  | AF => Undefined
  | ZF => Defined (v =? 0)
  | SF => Defined (sign_bit z v)
  | PF => Defined (even_parity v)
  end.

(** The function [undefined_flags] leaves every flag undefined, as
    `div` and `idiv` do. *)
Definition undefined_flags (f : flag) : flag_effect := Undefined.

(** The function [condition_holds] evaluates a condition on the
    current flags. *)
Definition condition_holds (c : condition) (fl : flag -> bool) : bool :=
  match c with
  | CondE => fl ZF
  | CondNE => negb (fl ZF)
  | CondB => fl CF
  | CondBE => fl CF || fl ZF
  | CondA => negb (fl CF || fl ZF)
  | CondAE => negb (fl CF)
  | CondL => xorb (fl SF) (fl OF)
  | CondLE => fl ZF || xorb (fl SF) (fl OF)
  | CondG => negb (fl ZF || xorb (fl SF) (fl OF))
  | CondGE => negb (xorb (fl SF) (fl OF))
  | CondS => fl SF
  | CondNS => negb (fl SF)
  | CondO => fl OF
  | CondNO => negb (fl OF)
  | CondP => fl PF
  | CondNP => negb (fl PF)
  end.

(** ## One instruction

    The function [step] executes one instruction. It reads its
    operands through [get_reg], writes its result through [set_reg],
    and updates the flags through [set_flags], so the rules for
    partial registers and undefined flags are those of
    Amd64Machine.v. *)

(** The function [source_value] reads a source operand at the size z
    as an unsigned integer. An immediate is reduced to the operand
    size, which gives a negative immediate its two's-complement
    pattern. *)
Definition source_value (z : size) (a : source) (s : machine) : Z :=
  match a with
  | SImm n => wrap z n
  | SReg r => get_reg z r s
  end.

(** The function [effective_address] computes the address that a
    memory operand denotes in the state s. The processor adds the
    displacement to the 64-bit content of the base register and keeps
    the low 64 bits of the sum. *)
Definition effective_address (a : address) (s : machine) : Z :=
  wrap S64 (get_reg S64 (address_base a) s + address_displacement a).

(** The function [accessible] decides whether every byte of an access
    of the size z at the address p is mapped in the state s. The bytes
    of an access are the addresses from p upward, and the model does
    not wrap them at the top of the address space. An access that
    crosses that boundary is therefore accessible only in a state that
    maps addresses beyond 64 bits, which no real state does. *)
Definition accessible (z : size) (p : Z) (s : machine) : bool :=
  all_mapped (size_bytes z) (mapped s) p.

(** The function [binary_value] computes the result pattern of a
    binary operation at the size z, where d is the destination's value
    and a is the source's value. *)
Definition binary_value (o : binary) (z : size) (d a : Z) : Z :=
  match o with
  | BAdd => wrap z (d + a)
  | BSub | BCmp => wrap z (d - a)
  | BAnd | BTest => Z.land d a
  | BOr => Z.lor d a
  | BXor => Z.lxor d a
  end.

(** The function [binary_flags] computes the flag effects of a binary
    operation on the same two values. An addition carries when the
    unsigned sum leaves the size, and a subtraction borrows when the
    source exceeds the destination. Both overflow when the exact
    signed result does not fit the size. The auxiliary carry is the
    carry or borrow of the low four bits. *)
Definition binary_flags (o : binary) (z : size) (d a : Z) : flag -> flag_effect :=
  let v := binary_value o z d a in
  match o with
  | BAdd =>
      arith_flags z v
        (size_modulus z <=? d + a)
        (negb (fits_signed z (signed_at z d + signed_at z a)))
        (16 <=? d mod 16 + a mod 16)
  | BSub | BCmp =>
      arith_flags z v
        (d <? a)
        (negb (fits_signed z (signed_at z d - signed_at z a)))
        (d mod 16 <? a mod 16)
  | BAnd | BTest | BOr | BXor => logic_flags z v
  end.

(** The function [binary_writes] says whether a binary operation
    stores its result. The comparisons `cmp` and `test` only set the
    flags. *)
Definition binary_writes (o : binary) : bool :=
  match o with
  | BCmp | BTest => false
  | BAdd | BSub | BAnd | BOr | BXor => true
  end.

(** The function [step] executes the instruction i in the state s,
    taking the value of every flag that i leaves undefined from the
    havoc h. An extending move whose source is not narrower than its
    destination, and a sign extension or division at the byte size,
    are outside the model. A division stops with [DivideError] where
    [divide_words] reports one. A load or a store stops with
    [MemoryFault] when a byte of its access is not mapped. A load
    writes its register by the rule of [set_reg], so a 32-bit load
    clears the upper half of its destination. *)
Definition step (h : havoc) (i : instr) (s : machine) : outcome :=
  match i with
  | IMov z a d => Next (set_reg z d (source_value z a s) s)
  | ILoad z a d =>
      let p := effective_address a s in
      if accessible z p s then Next (set_reg z d (read_at z (bytes s) p) s)
      else Fault MemoryFault
  | IStore z r a =>
      let p := effective_address a s in
      if accessible z p s
      then Next (set_bytes (write_at z (bytes s) p (get_reg z r s)) s)
      else Fault MemoryFault
  | IMovzx za zd a d =>
      if size_ltb za zd then Next (set_reg zd d (get_reg za a s) s)
      else Fault Unmodeled
  | IMovsx za zd a d =>
      if size_ltb za zd then Next (set_reg zd d (signed_at za (get_reg za a s)) s)
      else Fault Unmodeled
  | IBinary o z a d =>
      let x := get_reg z d s in
      let y := source_value z a s in
      let s' := if binary_writes o then set_reg z d (binary_value o z x y) s else s in
      Next (set_flags h (binary_flags o z x y) s')
  | IUnary UNeg z d =>
      let x := get_reg z d s in
      let v := wrap z (- x) in
      Next (set_flags h
              (arith_flags z v
                 (negb (x =? 0))
                 (negb (fits_signed z (- signed_at z x)))
                 (negb (x mod 16 =? 0)))
              (set_reg z d v s))
  | IUnary UNot z d =>
      Next (set_reg z d (size_modulus z - 1 - get_reg z d s) s)
  | ISet c d =>
      Next (set_reg S8 d (if condition_holds c (flags s) then 1 else 0) s)
  | IExtend z =>
      match z with
      | S8 => Fault Unmodeled
      | S16 | S32 | S64 => Next (set_reg z RDX (sign_fill z (get_reg z RAX s)) s)
      end
  | IDivide sg z c =>
      match z with
      | S8 => Fault Unmodeled
      | S16 | S32 | S64 =>
          match divide_words sg z (get_reg z RDX s) (get_reg z RAX s) (get_reg z c s) with
          | Some qr =>
              Next (set_flags h undefined_flags
                      (set_reg z RDX (snd qr) (set_reg z RAX (fst qr) s)))
          | None => Fault DivideError
          end
      end
  end.

(** ## Sequences

    A straight-line sequence executes its instructions in order and
    stops at the first fault. Each instruction may leave flags
    undefined, and each such instruction may receive a different
    havoc. The relation [runs] therefore describes every execution
    that some choice of havocs allows, and a theorem about a sequence
    is a statement about all of them. *)

(** The relation [runs] holds of a sequence, a starting state and an
    outcome when executing the sequence from that state can produce
    that outcome. *)
Inductive runs : list instr -> machine -> outcome -> Prop :=
| runs_done (s : machine) :
    runs [] s (Next s)
  (* the empty sequence completes in the state where it starts *)
| runs_step (h : havoc) (i : instr) (rest : list instr) (s s' : machine) (o : outcome) :
    step h i s = Next s' -> runs rest s' o -> runs (i :: rest) s o
  (* the first instruction completes and the rest runs from its state *)
| runs_fault (h : havoc) (i : instr) (rest : list instr) (s : machine) (f : fault) :
    step h i s = Fault f -> runs (i :: rest) s (Fault f).
  (* the first instruction stops the sequence *)

(** The function [run] executes a sequence with the same havoc at every
    instruction. It computes one of the executions that [runs]
    describes, which makes the model testable by evaluation and shows
    that every sequence has an execution. *)
Fixpoint run (h : havoc) (code : list instr) (s : machine) : outcome :=
  match code with
  | [] => Next s
  | i :: rest =>
      match step h i s with
      | Next s' => run h rest s'
      | Fault f => Fault f
      end
  end.

(** A sequence [establishes] a relation between its starting state and
    its final state when every execution from a state that satisfies
    the precondition P completes, and completes in a state that Q
    relates to the starting state. This is a [[hoare-triple]] for total
    correctness of straight-line code under every choice of undefined
    flags. *)
Definition establishes (P : machine -> Prop) (code : list instr)
    (Q : machine -> machine -> Prop) : Prop :=
  forall s o, P s -> runs code s o -> exists s', o = Next s' /\ Q s s'.

(** ## Facts about sequences

    A proof about a long sequence splits it into fragments, proves
    each fragment separately and joins the results. These lemmas give
    the rules for splitting an execution and for joining two
    fragments. *)

(** The computed execution is one of the executions of the sequence. *)
Lemma run_runs (h : havoc) (code : list instr) (s : machine) :
  runs code s (run h code s).
Proof.
  revert s; induction code as [|i code IH]; intro s; simpl.
  - constructor.
  - destruct (step h i s) eqn:E.
    + eapply runs_step; [exact E | apply IH].
    + eapply runs_fault; exact E.
Qed.

(** The empty sequence has only one execution. *)
Lemma runs_nil_inv (s : machine) (o : outcome) :
  runs [] s o -> o = Next s.
Proof.
  intro H; inversion H; reflexivity.
Qed.

(** An execution of a non-empty sequence begins with one step of its
    first instruction under some havoc. Either that step completes and
    the rest of the sequence produces the outcome, or that step faults
    and its fault is the outcome. *)
Lemma runs_cons_inv (i : instr) (rest : list instr) (s : machine) (o : outcome) :
  runs (i :: rest) s o ->
  exists h,
    (exists s', step h i s = Next s' /\ runs rest s' o)
    \/ (exists f, step h i s = Fault f /\ o = Fault f).
Proof.
  intro H; inversion H; subst; eauto.
Qed.

(** An execution of two sequences in a row either completes the first
    and continues with the second, or stops in the first. *)
Lemma runs_app_inv (code code' : list instr) (s : machine) (o : outcome) :
  runs (code ++ code') s o ->
  (exists s', runs code s (Next s') /\ runs code' s' o)
  \/ (exists f, runs code s (Fault f) /\ o = Fault f).
Proof.
  revert s o; induction code as [|i code IH]; intros s o H; simpl in H.
  - left; exists s; split; [constructor | exact H].
  - apply runs_cons_inv in H; destruct H as [h [[t [E H]] | [f [E ->]]]].
    + destruct (IH _ _ H) as [[u [Hu Hrest]] | [f [Hf ->]]].
      * left; exists u; split; [eapply runs_step; eauto | exact Hrest].
      * right; exists f; split; [eapply runs_step; eauto | reflexivity].
    + right; exists f; split; [eapply runs_fault; eauto | reflexivity].
Qed.

(** Two executions in a row form an execution of the concatenated
    sequence. *)
Lemma runs_app (code code' : list instr) (s s' : machine) (o : outcome) :
  runs code s (Next s') -> runs code' s' o -> runs (code ++ code') s o.
Proof.
  intros H; remember (Next s') as result eqn:E.
  induction H; inversion E; subst; simpl; intro Hrest.
  - exact Hrest.
  - eapply runs_step; [eassumption | apply IHruns; reflexivity || assumption].
Qed.

(** Two fragments compose. The first fragment must establish, from the
    precondition P, a state that satisfies the precondition of the
    second, and the relation of the whole is the composition of the
    relations of the parts. *)
Lemma establishes_app (P P' : machine -> Prop) (code code' : list instr)
    (Q Q' : machine -> machine -> Prop) :
  establishes P code Q ->
  establishes P' code' Q' ->
  (forall s s', P s -> Q s s' -> P' s') ->
  establishes P (code ++ code')
    (fun s s'' => exists s', Q s s' /\ Q' s' s'').
Proof.
  intros H H' Hpre s o HP Hr.
  destruct (runs_app_inv _ _ _ _ Hr) as [[t [Ht Hrest]] | [f [Hf ->]]].
  - destruct (H _ _ HP Ht) as [u [E HQ]]; inversion E; subst u.
    destruct (H' _ _ (Hpre _ _ HP HQ) Hrest) as [v [E' HQ']].
    exists v; split; [exact E' | exists t; auto].
  - destruct (H _ _ HP Hf) as [t [E _]]; discriminate.
Qed.

(** A fragment's precondition can be strengthened and its relation
    weakened. *)
Lemma establishes_weaken (P P' : machine -> Prop) (code : list instr)
    (Q Q' : machine -> machine -> Prop) :
  establishes P code Q ->
  (forall s, P' s -> P s) ->
  (forall s s', P' s -> Q s s' -> Q' s s') ->
  establishes P' code Q'.
Proof.
  intros H Hpre Hpost s o HP Hr.
  destruct (H _ _ (Hpre _ HP) Hr) as [t [E HQ]].
  exists t; split; [exact E | eapply Hpost; eauto].
Qed.

(** The empty sequence establishes the identity relation. *)
Lemma establishes_nil (P : machine -> Prop) :
  establishes P [] (fun s s' => s' = s).
Proof.
  intros s o HP Hr; exists s; split; [apply runs_nil_inv; exact Hr | reflexivity].
Qed.

(** ## Facts about single steps

    These lemmas record properties of [step] that hold for every
    instruction. They are checks on the model and are also what a
    frame argument about untouched registers uses. *)

(** An instruction keeps a well-formed state well-formed. *)
Lemma step_well_formed (h : havoc) (i : instr) (s s' : machine) :
  well_formed s -> step h i s = Next s' -> well_formed s'.
Proof.
  intros H E; destruct i; cbn [step] in E;
    repeat match type of E with
    | context [if ?b then _ else _] => destruct b eqn:?
    | context [match ?z with S8 => _ | _ => _ end] => destruct z
    | context [match ?o with UNeg => _ | UNot => _ end] => destruct o
    | context [match ?q with Some _ => _ | None => _ end] => destruct q
    end;
    inversion E; subst;
    repeat first [apply set_flags_well_formed | apply set_reg_well_formed];
    exact H.
Qed.

(** The function [writes] lists the registers that an instruction may
    change. *)
Definition writes (i : instr) : list gpr :=
  match i with
  | IMov _ _ d | ILoad _ _ d | IMovzx _ _ _ d | IMovsx _ _ _ d | IUnary _ _ d
  | ISet _ d => [d]
  | IStore _ _ _ => []
  | IBinary o _ _ d => if binary_writes o then [d] else []
  | IExtend _ => [RDX]
  | IDivide _ _ _ => [RAX; RDX]
  end.

(** An instruction changes no register outside its [writes] list. *)
Lemma step_frame (h : havoc) (i : instr) (s s' : machine) (r : gpr) :
  step h i s = Next s' -> ~ In r (writes i) -> regs s' r = regs s r.
Proof.
  destruct i; cbn [step writes];
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?
    | |- context [match ?z with S8 => _ | _ => _ end] => destruct z
    | |- context [match ?o with UNeg => _ | UNot => _ end] => destruct o
    | |- context [match ?q with Some _ => _ | None => _ end] => destruct q
    end;
    intros E H; inversion E; subst;
    repeat rewrite regs_set_flags;
    repeat rewrite regs_set_reg_other by (simpl in H; intuition congruence);
    reflexivity.
Qed.

(** A sequence changes no register that none of its instructions
    writes. *)
Lemma runs_frame (code : list instr) (s s' : machine) (r : gpr) :
  runs code s (Next s') ->
  (forall i, In i code -> ~ In r (writes i)) ->
  regs s' r = regs s r.
Proof.
  intro H; remember (Next s') as result eqn:E.
  induction H; inversion E; subst; intro Hnone.
  - reflexivity.
  - transitivity (regs s'0 r).
    + apply IHruns; [reflexivity | intros j Hj; apply Hnone; right; exact Hj].
    + eapply step_frame; [eassumption | apply Hnone; left; reflexivity].
Qed.

(** An undefined flag cannot change a register. Two steps of the same
    instruction from the same state, under two different havocs,
    either both complete with equal register contents or both stop
    with the same fault. *)
Lemma step_regs_havoc (h h' : havoc) (i : instr) (s : machine) :
  match step h i s, step h' i s with
  | Next s1, Next s2 => forall r, regs s1 r = regs s2 r
  | Fault f1, Fault f2 => f1 = f2
  | _, _ => False
  end.
Proof.
  destruct i; cbn [step];
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b
    | |- context [match ?z with S8 => _ | _ => _ end] => destruct z
    | |- context [match ?o with UNeg => _ | UNot => _ end] => destruct o
    | |- context [match ?q with Some _ => _ | None => _ end] => destruct q
    end; reflexivity.
Qed.

(** ## Facts about memory

    Only a store changes the content of memory, and no instruction
    changes which addresses are mapped. These lemmas state both facts
    for one step and for a sequence. A proof about code that computes
    in registers uses them to carry the frame's content across that
    code. *)

(** The function [stores] says whether an instruction may change the
    content of memory. *)
Definition stores (i : instr) : bool :=
  match i with
  | IStore _ _ _ => true
  | _ => false
  end.

(** An instruction does not change which addresses are mapped. *)
Lemma step_mapped (h : havoc) (i : instr) (s s' : machine) :
  step h i s = Next s' -> mapped s' = mapped s.
Proof.
  intro E; destruct i; cbn [step] in E;
    repeat match type of E with
    | context [if ?b then _ else _] => destruct b eqn:?
    | context [match ?z with S8 => _ | _ => _ end] => destruct z
    | context [match ?o with UNeg => _ | UNot => _ end] => destruct o
    | context [match ?q with Some _ => _ | None => _ end] => destruct q
    end;
    inversion E; subst;
    repeat first [rewrite mapped_set_reg | rewrite mapped_set_flags |
                  rewrite mapped_set_bytes];
    reflexivity.
Qed.

(** A sequence does not change which addresses are mapped. *)
Lemma runs_mapped (code : list instr) (s s' : machine) :
  runs code s (Next s') -> mapped s' = mapped s.
Proof.
  intro H; remember (Next s') as result eqn:E.
  induction H; inversion E; subst.
  - reflexivity.
  - transitivity (mapped s'0).
    + apply IHruns; reflexivity.
    + eapply step_mapped; eassumption.
Qed.

(** An instruction that is not a store does not change the content of
    memory. *)
Lemma step_bytes (h : havoc) (i : instr) (s s' : machine) :
  step h i s = Next s' -> stores i = false -> bytes s' = bytes s.
Proof.
  intros E H; destruct i; cbn [stores] in H; try discriminate;
    cbn [step] in E;
    repeat match type of E with
    | context [if ?b then _ else _] => destruct b eqn:?
    | context [match ?z with S8 => _ | _ => _ end] => destruct z
    | context [match ?o with UNeg => _ | UNot => _ end] => destruct o
    | context [match ?q with Some _ => _ | None => _ end] => destruct q
    end;
    inversion E; subst;
    repeat first [rewrite bytes_set_reg | rewrite bytes_set_flags];
    reflexivity.
Qed.

(** A sequence without a store does not change the content of
    memory. *)
Lemma runs_bytes (code : list instr) (s s' : machine) :
  runs code s (Next s') ->
  (forall i, In i code -> stores i = false) ->
  bytes s' = bytes s.
Proof.
  intro H; remember (Next s') as result eqn:E.
  induction H; inversion E; subst; intro Hnone.
  - reflexivity.
  - transitivity (bytes s'0).
    + apply IHruns; [reflexivity | intros j Hj; apply Hnone; right; exact Hj].
    + eapply step_bytes; [eassumption | apply Hnone; left; reflexivity].
Qed.

(** A fragment without a store leaves the memory as it found it. This
    lemma adds that fact to whatever relation the fragment establishes,
    so a theorem that was proved about registers alone extends to a
    state with memory. *)
Lemma establishes_memory (P : machine -> Prop) (code : list instr)
    (Q : machine -> machine -> Prop) :
  establishes P code Q ->
  (forall i, In i code -> stores i = false) ->
  establishes P code
    (fun s s' => Q s s' /\ bytes s' = bytes s /\ mapped s' = mapped s).
Proof.
  intros H Hnone s o HP Hr.
  destruct (H _ _ HP Hr) as [t [E HQ]].
  exists t; split; [exact E | split; [exact HQ | split]].
  - eapply runs_bytes; [rewrite <- E; exact Hr | exact Hnone].
  - eapply runs_mapped; rewrite <- E; exact Hr.
Qed.

(** ## Facts about loads and stores

    These lemmas describe one load and one store as fragments, in the
    form that [establishes_app] composes. Each has the precondition
    that the bytes of its access are mapped, and each says exactly
    what the instruction changes. *)

(** A load from accessible memory completes. It leaves the bytes that
    it read in its destination register, and it changes neither
    another register nor the memory. *)
Lemma load_spec (z : size) (a : address) (d : gpr) :
  establishes (fun s => accessible z (effective_address a s) s = true)
    [ILoad z a d]
    (fun s s' =>
       s' = set_reg z d (read_at z (bytes s) (effective_address a s)) s).
Proof.
  intros s o HP Hr.
  apply runs_cons_inv in Hr; destruct Hr as [h [[t [E Hr]] | [f [E ->]]]].
  - cbn [step] in E; rewrite HP in E; inversion E; subst t.
    eexists; split; [apply runs_nil_inv; exact Hr | reflexivity].
  - cbn [step] in E; rewrite HP in E; discriminate.
Qed.

(** A store to accessible memory completes. It writes the low part of
    its register to the bytes of its access, and it changes neither a
    register nor a flag. *)
Lemma store_spec (z : size) (r : gpr) (a : address) :
  establishes (fun s => accessible z (effective_address a s) s = true)
    [IStore z r a]
    (fun s s' =>
       s' = set_bytes
              (write_at z (bytes s) (effective_address a s) (get_reg z r s)) s).
Proof.
  intros s o HP Hr.
  apply runs_cons_inv in Hr; destruct Hr as [h [[t [E Hr]] | [f [E ->]]]].
  - cbn [step] in E; rewrite HP in E; inversion E; subst t.
    eexists; split; [apply runs_nil_inv; exact Hr | reflexivity].
  - cbn [step] in E; rewrite HP in E; discriminate.
Qed.

(** A load from memory that is not accessible stops with a memory
    fault, under every havoc. *)
Lemma load_faults (h : havoc) (z : size) (a : address) (d : gpr) (s : machine) :
  accessible z (effective_address a s) s = false ->
  step h (ILoad z a d) s = Fault MemoryFault.
Proof.
  intro H; cbn [step]; rewrite H; reflexivity.
Qed.

(** A store to memory that is not accessible stops with a memory
    fault, under every havoc. *)
Lemma store_faults (h : havoc) (z : size) (r : gpr) (a : address) (s : machine) :
  accessible z (effective_address a s) s = false ->
  step h (IStore z r a) s = Fault MemoryFault.
Proof.
  intro H; cbn [step]; rewrite H; reflexivity.
Qed.
